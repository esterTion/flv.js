/*
 * @author esterTion <esterTionCN@gmail.com>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import Log from '../utils/logger.js';
import SPSParser from './sps-parser.js';
import DemuxErrors from './demux-errors.js';
import MediaInfo from '../core/media-info.js';
import { IllegalStateException } from '../utils/exception.js';


function ReadBig16(array, index) {
    return ((array[index] << 8) |
        (array[index + 1]));
}
function ReadBig32(array, index) {
    return ReadBig16(array, index) * 65536 + ReadBig16(array, index + 2);
}
function ReadBig64(array, index) {
    return ReadBig32(array, index) * 4294967296 + ReadBig32(array, index + 4);
}

function ReadString(uintarray, index, length) {
    let arr = [];
    for (let i = 0; i < length; i++) {
        arr.push(uintarray[index + i]);
    }
    try {
        return decodeURIComponent(escape(String.fromCharCode.apply(null, arr)));
    } catch (e) {
        return '';
    }
}

function boxInfo(uintarr, index) {
    let boxSize = ReadBig32(uintarr, index);
    let boxName = ReadString(uintarr, index + 4, 4);
    let boxHeadSize = 8;
    if (boxSize == 1) {
        boxSize = ReadBig64(uintarr, index + 8);
        boxHeadSize = 16;
    }
    let fullyLoaded = uintarr.length >= (index + boxSize);
    if (boxSize == 0)
        return {
            size: 8,
            headSize: boxHeadSize,
            name: '',
            fullyLoaded: true
        };
    return {
        size: boxSize,
        headSize: boxHeadSize,
        name: boxName,
        fullyLoaded: fullyLoaded
    };
}


let esdsIDs = {
    3: 'esDescription',
    4: 'decConfigDescription',
    5: 'decSpecificDescription'
};
function esdsParse(parent, array, index) {
    let descType = array[index];
    let offset = 1;
    let size = 0;
    let byteRead = array[index + offset];
    while (byteRead & 0x80) {
        size = (byteRead & 0x7f) << 7;
        offset++;
        byteRead = array[index + offset];
    }
    size += byteRead & 0x7f;
    offset++;
    switch (descType) {
        case 3: {
            //esDesc
            let trackID = ReadBig16(array, index + offset);
            let flags = array[index + offset + 2];
            offset += 3;
            parent[esdsIDs[descType]] = {
                size,
                trackID
            };
            esdsParse(parent[esdsIDs[descType]], array, index + offset);
            break;
        }
        case 4: {
            //decConfig
            let oti = array[index + offset];
            let streamType = array[index + offset + 1];
            let bufferSize = ReadBig32(array, index + offset + 1) & 0xffffff;
            let maxBitrate = ReadBig32(array, index + offset + 5);
            let avgBitrate = ReadBig32(array, index + offset + 9);
            parent[esdsIDs[descType]] = {
                oti,
                streamType,
                bufferSize,
                maxBitrate,
                avgBitrate,
            };
            esdsParse(parent[esdsIDs[descType]], array, index + offset + 13);
            break;
        }
        case 5: {
            //decSpecfic
            let data = Array.from(new Uint8Array(array.buffer, array.byteOffset + index + offset, size));
            let originalAudioObjectType = data[0] >>> 3;
            let samplingIndex = ((data[0] & 0x07) << 1) | (data[1] >>> 7);
            let channelConfig = (data[1] & 0x78) >>> 3;
            parent[esdsIDs[descType]] = {
                data,
                originalAudioObjectType,
                samplingIndex,
                channelConfig
            };
            break;
        }
    }
}


class MP4Demuxer {

    constructor(probeData, config) {
        this.TAG = 'MP4Demuxer';

        this._config = config;

        this._onError = null;
        this._onMediaInfo = null;
        this._onTrackMetadata = null;
        this._onDataAvailable = null;

        this._dataOffset = probeData.dataOffset;
        this._firstParse = true;
        this._dispatch = false;
        this._mdatEnd = 0;

        this._hasAudio = probeData.hasAudioTrack;
        this._hasVideo = probeData.hasVideoTrack;

        this._audioInitialMetadataDispatched = false;
        this._videoInitialMetadataDispatched = false;

        this._mediaInfo = new MediaInfo();
        this._mediaInfo.hasAudio = this._hasAudio;
        this._mediaInfo.hasVideo = this._hasVideo;
        this._metadata = null;
        this._audioMetadata = null;
        this._videoMetadata = null;

        this._naluLengthSize = 4;
        this._timestampBase = 0;  // int32, in milliseconds
        this._timescale = 1000;
        this._duration = 0;  // int32, in milliseconds
        this._durationOverrided = false;
        this._referenceFrameRate = {
            fixed: true,
            fps: 23.976,
            fps_num: 23976,
            fps_den: 1000
        };

        this._flvSoundRateTable = [5500, 11025, 22050, 44100, 48000];

        this._mpegSamplingRates = [
            96000, 88200, 64000, 48000, 44100, 32000,
            24000, 22050, 16000, 12000, 11025, 8000, 7350
        ];

        this._mpegAudioV10SampleRateTable = [44100, 48000, 32000, 0];
        this._mpegAudioV20SampleRateTable = [22050, 24000, 16000, 0];
        this._mpegAudioV25SampleRateTable = [11025, 12000, 8000, 0];

        this._mpegAudioL1BitRateTable = [0, 32, 64, 96, 128, 160, 192, 224, 256, 288, 320, 352, 384, 416, 448, -1];
        this._mpegAudioL2BitRateTable = [0, 32, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 384, -1];
        this._mpegAudioL3BitRateTable = [0, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, -1];

        this._videoTrack = { type: 'video', id: 1, sequenceNumber: 0, samples: [], length: 0 };
        this._audioTrack = { type: 'audio', id: 2, sequenceNumber: 0, samples: [], length: 0 };

        this._littleEndian = (function () {
            let buf = new ArrayBuffer(2);
            (new DataView(buf)).setInt16(0, 256, true);  // little-endian write
            return (new Int16Array(buf))[0] === 256;  // platform-spec read, if equal then LE
        })();
    }

    destroy() {
        this._mediaInfo = null;
        this._metadata = null;
        this._audioMetadata = null;
        this._videoMetadata = null;
        this._videoTrack = null;
        this._audioTrack = null;

        this._onError = null;
        this._onMediaInfo = null;
        this._onTrackMetadata = null;
        this._onDataAvailable = null;
    }

    static probe(buffer) {
        let data = new Uint8Array(buffer);
        let mismatch = { match: false };

        // no ftyp box found, mismatch
        let ftyp = boxInfo(data, 0);
        if (ftyp.name != 'ftyp' || !ftyp.fullyLoaded) {
            return mismatch;
        }

        let offset = ftyp.size;
        let box = boxInfo(data, offset);

        //skip all non-moov box until stream ends
        while (box.fullyLoaded) {
            if (box.name == 'moov')
                break;
            offset += box.size;
            box = boxInfo(data, offset);
        }
        //no moov found in file header, not supported at this time
        if (box.name != 'moov') {
            return mismatch;
        }

        return {
            match: true,
            enoughData: box.fullyLoaded,
            consumed: offset,
            dataOffset: offset,
        };
    }

    _parseMoov(data) {
        const containerBox = [
            'moov',
            'trak',
            'mdia',
            'minf',
            'stbl'
        ];

        function parseMoov(parent, data, index, length) {
            let offset = 0;
            while (offset < length) {
                let box = boxInfo(data, index + offset);
                if (containerBox.indexOf(box.name) !== -1) {
                    parent[box.name] = parent[box.name] || [];
                    parent[box.name].push({});
                    parseMoov(parent[box.name][parent[box.name].length - 1], data, index + offset + 8, box.size - 8);
                } else {
                    let body;
                    switch (box.name) {
                        case 'mvhd': {
                            /*
                            mvhd struct
                            version 1   0
                            flags   3   1
                            create  4   4
                            modifi  4   8
                            Tscale  4   12
                            dura    4   16
                            rate    4   20
                            volume  2   24
                            reserve 10  26
                            matrik  36  36
                            preT    4   72
                            preD    4   76
                            poster  4   80
                            selectT 4   84
                            selectD 4   88
                            current 4   92
                            nextID  4   96
                            */
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 8, box.size - 8);
                            let timeScale = ReadBig32(body, 12);
                            let duration = ReadBig32(body, 16);
                            parent[box.name] = {
                                timeScale,
                                duration
                            };
                            break;
                        }
                        case 'tkhd': {
                            /*
                            tkhd struct
                            version 1   0
                            flags   3   1
                            create  4   4
                            modifi  4   8
                            trackID 4   12
                            reserve 4   16
                            dura    4   20
                            reserve 8   24
                            layer   2   32
                            group   2   34
                            volume  2   36
                            reserve 2   38
                            matrix  36  40
                            Twidth  4   76
                            Theight 4   80
                            */
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 8, box.size - 8);
                            let flags = {
                                trackEnbaled: body[3] & 1,
                                trackInMovie: (body[3] & 2) >> 1,
                                trackInPreview: (body[3] & 4) >> 2,
                                trackInPoster: (body[3] & 8) >> 3
                            };
                            let trackID = ReadBig32(body, 12);
                            let duration = ReadBig32(body, 20);
                            let group = ReadBig16(body, 34);
                            let trackWidth = parseFloat(ReadBig16(body, 72) + '.' + ReadBig16(body, 74));
                            let trackHeight = parseFloat(ReadBig16(body, 76) + '.' + ReadBig16(body, 78));

                            parent[box.name] = {
                                flags,
                                trackID,
                                duration,
                                group,
                                trackWidth,
                                trackHeight
                            };
                            break;
                        }
                        case 'mdhd': {
                            /*
                            mdhd struct
                            version 1   0
                            flags   3   1
                            create  4   4
                            modifi  4   8
                            Tscale  4   12
                            dura    4   16
                            lang    2   20
                            quality 2   22
                            */
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 8, box.size - 8);
                            let timeScale = ReadBig32(body, 12);
                            let duration = ReadBig32(body, 16);
                            let language = ReadBig16(body, 20);
                            let quality = ReadBig16(body, 22);

                            parent[box.name] = {
                                timeScale,
                                duration,
                                language,
                                quality
                            };
                            break;
                        }
                        case 'stsd': {
                            parent[box.name] = parent[box.name] || [];
                            parent[box.name].push({});
                            parseMoov(parent[box.name][parent[box.name].length - 1], data, index + offset + 16, box.size - 16);
                            break;
                        }
                        case 'avc1': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 8, box.size - 8);
                            let dataReferenceIndex = ReadBig32(body, 4);
                            let version = ReadBig16(body, 8);
                            let revisionLevel = ReadBig16(body, 10);
                            let vendor = ReadBig32(body, 12);
                            let temporalQuality = ReadBig32(body, 16);
                            let spatialQuality = ReadBig32(body, 20);
                            let width = ReadBig16(body, 24);
                            let height = ReadBig16(body, 26);
                            let horizontalResolution = parseFloat(ReadBig16(body, 28) + '.' + ReadBig16(body, 30));
                            let verticalResolution = parseFloat(ReadBig16(body, 32) + '.' + ReadBig16(body, 34));
                            let dataSize = ReadBig32(body, 36);
                            let frameCount = ReadBig16(body, 40);
                            let compressorName = ReadString(body, 42, 32);
                            let depth = ReadBig16(body, 74);
                            let colorTableID = ReadBig16(body, 76);

                            parent[box.name] = {
                                dataReferenceIndex,
                                version,
                                revisionLevel,
                                vendor,
                                temporalQuality,
                                spatialQuality,
                                width,
                                height,
                                horizontalResolution,
                                verticalResolution,
                                dataSize,
                                frameCount,
                                compressorName,
                                depth,
                                colorTableID,
                                extensions: {}
                            };
                            parseMoov(parent[box.name].extensions, data, index + offset + 86, box.size - 86);
                            break;
                        }
                        case 'avcC': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 8, box.size - 8);
                            let configurationVersion = body[0];
                            let avcProfileIndication = body[1];
                            let profile_compatibility = body[2];
                            let AVCLevelIndication = body[3];
                            let lengthSizeMinusOne = body[4] & 0x3;
                            let nb_nalus = body[5] & 0x1f;
                            let SPS = new Array(nb_nalus);
                            let recordLength;
                            let boxOffset = 6;
                            for (let i = 0; i < nb_nalus; i++) {
                                recordLength = ReadBig16(body, offset);
                                boxOffset += 2;
                                SPS[i] = SPSParser.parseSPS(new Uint8Array(data.buffer, data.byteOffset + index + offset + 8 + boxOffset, recordLength));
                                let codecString = 'avc1.';
                                let codecArray = body.subarray(boxOffset + 1, boxOffset + 4);
                                for (let j = 0; j < 3; j++) {
                                    let h = codecArray[j].toString(16);
                                    if (h.length < 2) {
                                        h = '0' + h;
                                    }
                                    codecString += h;
                                }
                                SPS[i].codecString = codecString;
                                boxOffset += recordLength;
                            }
                            nb_nalus = body[boxOffset];
                            let PPS = new Array(nb_nalus);
                            boxOffset++;
                            for (let i = 0; i < nb_nalus; i++) {
                                recordLength = ReadBig16(body, offset);
                                boxOffset += 2;
                                //ignoring PPS
                                boxOffset += recordLength;
                            }
                            parent[box.name] = {
                                configurationVersion,
                                avcProfileIndication,
                                profile_compatibility,
                                AVCLevelIndication,
                                lengthSizeMinusOne,
                                SPS,
                                data: body
                            };
                            break;
                        }
                        case 'mp4a': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 8, box.size - 8);
                            let dataReferenceIndex = ReadBig32(body, 4);
                            let version = ReadBig16(body, 8);
                            let revisionLevel = ReadBig16(body, 10);
                            let vendor = ReadBig32(body, 12);
                            let channels = ReadBig16(body, 16);
                            let sampleSize = ReadBig16(body, 18);
                            let compressionID = ReadBig16(body, 20);
                            let packetSize = ReadBig16(body, 22);
                            let sampleRate = ReadBig16(body, 24);
                            //unknown two bytes here???
                            parent[box.name] = {
                                dataReferenceIndex,
                                version,
                                revisionLevel,
                                vendor,
                                channels,
                                sampleSize,
                                compressionID,
                                packetSize,
                                sampleRate,
                                extensions: {}
                            };
                            parseMoov(parent[box.name].extensions, data, index + offset + 36, box.size - 36);
                            break;
                        }
                        case 'esds': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 8, box.size - 8);
                            let esdsData = {};
                            esdsParse(esdsData, body, 4);
                            parent[box.name] = esdsData;
                            break;
                        }
                        case 'stts': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 12, box.size - 12);
                            let entryCount = ReadBig32(body, 0);
                            let sampleTable = new Array(entryCount);
                            let boxOffset = 4;
                            for (let i = 0; i < entryCount; i++) {
                                let sampleCount = ReadBig32(body, boxOffset);
                                let sampleDuration = ReadBig32(body, boxOffset + 4);
                                sampleTable[i] = {
                                    sampleCount, sampleDuration
                                };
                                boxOffset += 8;
                            }
                            parent[box.name] = sampleTable;
                            break;
                        }
                        case 'ctts': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 12, box.size - 12);
                            let entryCount = ReadBig32(body, 0);
                            let sampleTable = new Array(entryCount);
                            let boxOffset = 4;
                            for (let i = 0; i < entryCount; i++) {
                                let sampleCount = ReadBig32(body, boxOffset);
                                let compositionOffset = ReadBig32(body, boxOffset + 4);
                                sampleTable[i] = {
                                    sampleCount, compositionOffset
                                };
                                boxOffset += 8;
                            }
                            parent[box.name] = sampleTable;
                            break;
                        }
                        case 'stss': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 12, box.size - 12);
                            let entryCount = ReadBig32(body, 0);
                            let sampleTable = new Array(entryCount);
                            let boxOffset = 4;
                            for (let i = 0; i < entryCount; i++) {
                                sampleTable[i] = ReadBig32(body, boxOffset);
                                boxOffset += 4;
                            }
                            parent[box.name] = sampleTable;
                            break;
                        }
                        case 'stsc': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 12, box.size - 12);
                            let entryCount = ReadBig32(body, 0);
                            let sampleTable = new Array(entryCount);
                            let boxOffset = 4;
                            for (let i = 0; i < entryCount; i++) {
                                let firstChunk = ReadBig32(body, boxOffset);
                                let samplesPerChunk = ReadBig32(body, boxOffset + 4);
                                let sampleDescID = ReadBig32(body, boxOffset + 8);
                                sampleTable[i] = {
                                    firstChunk, samplesPerChunk, sampleDescID
                                };
                                boxOffset += 12;
                            }
                            parent[box.name] = sampleTable;
                            break;
                        }
                        case 'stsz': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 12, box.size - 12);
                            let sampleSize = ReadBig32(body, 0);
                            let entryCount = ReadBig32(body, 4);
                            let sampleTable = new Array(entryCount);
                            let boxOffset = 8;
                            for (let i = 0; i < entryCount; i++) {
                                sampleTable[i] = ReadBig32(body, boxOffset);
                                boxOffset += 4;
                            }
                            parent[box.name] = {
                                sampleSize,
                                sampleTable
                            };
                            break;
                        }
                        case 'stco': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 12, box.size - 12);
                            let entryCount = ReadBig32(body, 0);
                            let sampleTable = new Array(entryCount);
                            let boxOffset = 4;
                            for (let i = 0; i < entryCount; i++) {
                                sampleTable[i] = ReadBig32(body, boxOffset);
                                boxOffset += 4;
                            }
                            parent[box.name] = sampleTable;
                            break;
                        }
                        case 'co64': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 12, box.size - 12);
                            let entryCount = ReadBig32(body, 0);
                            let sampleTable = new Array(entryCount);
                            let boxOffset = 4;
                            for (let i = 0; i < entryCount; i++) {
                                sampleTable[i] = ReadBig64(body, boxOffset);
                                boxOffset += 8;
                            }
                            parent['stco'] = sampleTable;
                            break;
                        }
                        case 'hdlr': {
                            body = new Uint8Array(data.buffer, data.byteOffset + index + offset + 12, box.size - 12);
                            let handler = ReadString(body, 4, 4);
                            parent[box.name] = {
                                handler
                            };
                            break;
                        }
                    }
                }
                offset += box.size;
            }
        }

        let moovData = {};
        parseMoov(moovData, data, 0, data.length);

        let trak = moovData.moov[0].trak;
        let tracks = {};
        let groups = [
            'video',
            'audio'
        ];
        for (let i = 0; i < trak.length; i++) {
            let track = trak[i];
            let group = -1;
            switch (track.mdia[0].hdlr.handler) {
                case 'vide': {
                    group = 0;
                    break;
                }
                case 'soun': {
                    group = 1;
                    break;
                }
            }
            if (!groups[group]) {
                continue;
            }
            if (tracks[groups[group]]) {
                Log.w(this.TAG, 'Found another ' + groups[group] + ' track, ignoring.');
                continue;
            }
            tracks[groups[group]] = track;
        }
        let mediaInfo = this._mediaInfo;
        mediaInfo.mimeType = 'video/mp4';
        mediaInfo.metadata = {
            duration: moovData.moov[0].mvhd.duration / moovData.moov[0].mvhd.timeScale * 1e3
        };
        mediaInfo.duration = this._duration;
        mediaInfo.hasVideo = this._hasVideo = tracks.video !== undefined;
        mediaInfo.hasAudio = this._hasAudio = tracks.audio !== undefined;
        let bitrateMapTrack = {};
        let maxDuration = 0;
        let chunkMap = [];
        let sampleTsMap = {};
        let codecs = [];
        let id = 1;
        let accurateDuration = [0];
        if (mediaInfo.hasVideo) {
            let sps = tracks.video.mdia[0].minf[0].stbl[0].stsd[0].avc1.extensions.avcC.SPS[0];
            mediaInfo.videoCodec = sps.codecString;
            codecs.push(mediaInfo.videoCodec);
            let stsz = tracks.video.mdia[0].minf[0].stbl[0].stsz.sampleTable;
            let stts = tracks.video.mdia[0].minf[0].stbl[0].stts;
            let stsc = tracks.video.mdia[0].minf[0].stbl[0].stsc;
            let stco = tracks.video.mdia[0].minf[0].stbl[0].stco;
            let timeScale = tracks.video.mdia[0].mdhd.timeScale;
            let sampleNumber = 0;
            let sampleTs = 0;
            let size = 0;
            bitrateMapTrack.video = new Array(Math.ceil(tracks.video.mdia[0].mdhd.duration / timeScale));
            sampleTsMap.video = [];
            for (let i = 0; i < stts.length; i++) {
                for (let j = 0; j < stts[i].sampleCount; j++) {
                    let time = (sampleTs / timeScale) | 0;
                    maxDuration = Math.max(time, maxDuration);
                    if (!bitrateMapTrack.video[time]) {
                        bitrateMapTrack.video[time] = 0;
                    }
                    bitrateMapTrack.video[time] += stsz[sampleNumber];
                    size += stsz[sampleNumber];
                    sampleTsMap.video.push({ ts: sampleTs, duration: stts[i].sampleDuration });
                    sampleTs += stts[i].sampleDuration;
                    sampleNumber++;
                }
            }
            let lastSample = sampleTsMap.video[sampleTsMap.video.length - 1];
            accurateDuration.push(Math.ceil((lastSample.ts + lastSample.duration) / timeScale * 1e3));
            let ctts = tracks.video.mdia[0].minf[0].stbl[0].ctts;
            let stss = tracks.video.mdia[0].minf[0].stbl[0].stss;
            let currentChunkRule = stsc[0];
            let nextChunkRule = stsc[1];
            let currentCtsRule = ctts[0];
            let currentCtsLeft = currentCtsRule.sampleCount;
            let cttsOffset = 0;
            let sampleToChunkOffset = 0;
            let chunkNumber = 1;
            sampleNumber = 0;
            let keyframesIndex = { times: [], filepositions: [] };
            for (let i = 0; i < stco.length; i++) {
                if (nextChunkRule != undefined && chunkNumber >= nextChunkRule.firstChunk) {
                    sampleToChunkOffset++;
                    currentChunkRule = nextChunkRule;
                    nextChunkRule = stsc[sampleToChunkOffset + 1];
                }
                let currentChunk = {
                    offset: stco[chunkNumber - 1],
                    type: 'video',
                    samples: []
                };
                for (let j = 0, sampleOffset = 0; j < currentChunkRule.samplesPerChunk; j++) {
                    if (currentCtsLeft == 0) {
                        currentCtsRule = ctts[++cttsOffset];
                        currentCtsLeft = currentCtsRule.sampleCount;
                    }
                    currentCtsLeft--;
                    let { ts, duration } = sampleTsMap.video[sampleNumber];
                    let cts = currentCtsRule.compositionOffset;
                    let size = stsz[sampleNumber++];
                    let isKeyframe = stss.indexOf(sampleNumber) != -1;
                    currentChunk.samples.push({
                        ts,
                        duration,
                        cts,
                        size,
                        isKeyframe
                    });

                    if (isKeyframe) {
                        keyframesIndex.times.push(this._timestampBase + ts / timeScale * 1e3);
                        keyframesIndex.filepositions.push(currentChunk.offset + sampleOffset);
                    }
                    sampleOffset += size;
                }
                chunkMap.push(currentChunk);
                chunkNumber++;
            }
            mediaInfo.videoDataRate = size / mediaInfo.metadata.duration * 8;
            mediaInfo.width = sps.present_size.width;
            mediaInfo.height = sps.present_size.height;
            mediaInfo.fps = sps.frame_rate.fps;
            mediaInfo.profile = sps.profile_string;
            mediaInfo.level = sps.level_string;
            mediaInfo.chromaFormat = sps.chroma_format_string;
            mediaInfo.sarNum = sps.sar_ratio.width;
            mediaInfo.sarDen = sps.sar_ratio.height;
            mediaInfo.hasKeyframesIndex = true;
            mediaInfo.keyframesIndex = keyframesIndex;

            let meta = {};
            meta.avcc = tracks.video.mdia[0].minf[0].stbl[0].stsd[0].avc1.extensions.avcC.data;
            meta.bitDepth = sps.bit_depth;
            meta.chromaFormat = sps.chroma_format;
            meta.codec = mediaInfo.videoCodec;
            meta.codecHeight = sps.codec_size.height;
            meta.codecWidth = sps.codec_size.width;
            meta.duration = (this._duration / 1e3 * timeScale) | 0;
            meta.timescale = timeScale;
            meta.frameRate = sps.frame_rate;
            meta.id = id++;
            meta.level = sps.level_string;
            meta.presentHeight = sps.present_size.height;
            meta.presentWidth = sps.present_size.width;
            meta.profile = sps.profile_string;
            meta.refSampleDuration = meta.timescale * (meta.frameRate.fps_den / meta.frameRate.fps_num);
            meta.sarRatio = sps.sar_ratio;
            meta.type = 'video';
            this._onTrackMetadata('video', meta);
            this._videoInitialMetadataDispatched = true;
            this._videoMetadata = meta;
        }
        if (mediaInfo.hasAudio) {
            let specDesc = tracks.audio.mdia[0].minf[0].stbl[0].stsd[0].mp4a.extensions.esds.esDescription.decConfigDescription.decSpecificDescription;
            mediaInfo.audioCodec = 'mp4a.40.' + specDesc.originalAudioObjectType;
            codecs.push(mediaInfo.audioCodec);
            mediaInfo.audioSampleRate = this._mpegSamplingRates[specDesc.samplingIndex];
            mediaInfo.audioChannelCount = specDesc.channelConfig;
            let stsz = tracks.audio.mdia[0].minf[0].stbl[0].stsz.sampleTable;
            let stts = tracks.audio.mdia[0].minf[0].stbl[0].stts;
            let stsc = tracks.audio.mdia[0].minf[0].stbl[0].stsc;
            let stco = tracks.audio.mdia[0].minf[0].stbl[0].stco;
            let timeScale = tracks.audio.mdia[0].mdhd.timeScale;
            let sampleNumber = 0;
            let sampleTs = 0;
            let size = 0;
            bitrateMapTrack.audio = new Array(Math.ceil(tracks.audio.mdia[0].mdhd.duration / timeScale));
            sampleTsMap.audio = [];
            for (let i = 0; i < stts.length; i++) {
                for (let j = 0; j < stts[i].sampleCount; j++) {
                    let time = (sampleTs / timeScale) | 0;
                    maxDuration = Math.max(time, maxDuration);
                    if (!bitrateMapTrack.audio[time]) {
                        bitrateMapTrack.audio[time] = 0;
                    }
                    bitrateMapTrack.audio[time] += stsz[sampleNumber];
                    size += stsz[sampleNumber];
                    sampleTsMap.audio.push({ ts: sampleTs, duration: stts[i].sampleDuration });
                    sampleTs += stts[i].sampleDuration;
                    sampleNumber++;
                }
            }
            let lastSample = sampleTsMap.audio[sampleTsMap.audio.length - 1];
            accurateDuration.push(Math.ceil((lastSample.ts + lastSample.duration) / timeScale * 1e3));
            let currentChunkRule = stsc[0];
            let nextChunkRule = stsc[1];
            let sampleToChunkOffset = 0;
            let chunkNumber = 1;
            sampleNumber = 0;
            for (let i = 0; i < stco.length; i++) {
                if (nextChunkRule != undefined && chunkNumber >= nextChunkRule.firstChunk) {
                    sampleToChunkOffset++;
                    currentChunkRule = nextChunkRule;
                    nextChunkRule = stsc[sampleToChunkOffset + 1];
                }
                let currentChunk = {
                    offset: stco[chunkNumber - 1],
                    type: 'audio',
                    samples: []
                };
                for (let j = 0; j < currentChunkRule.samplesPerChunk; j++) {
                    currentChunk.samples.push({
                        ts: sampleTsMap.audio[sampleNumber].ts,
                        duration: sampleTsMap.audio[sampleNumber].duration,
                        size: stsz[sampleNumber++]
                    });
                }
                chunkMap.push(currentChunk);
                chunkNumber++;
            }
            mediaInfo.audioDataRate = size / mediaInfo.metadata.duration * 8;
            let meta = {};
            meta.type = 'audio';
            meta.audioSampleRate = mediaInfo.audioSampleRate;
            meta.channelCount = mediaInfo.audioChannelCount;
            meta.codec = mediaInfo.audioCodec;
            meta.originalCodec = meta.codec;
            meta.config = specDesc.data;
            meta.duration = (this._duration / 1e3 * timeScale) | 0;
            meta.id = id++;
            meta.refSampleDuration = 1024 / meta.audioSampleRate * timeScale;
            meta.timescale = timeScale;
            this._onTrackMetadata('audio', meta);
            this._audioInitialMetadataDispatched = true;
            this._audioMetadata = meta;
        }
        mediaInfo.accurateDuration = Math.max.apply(null, accurateDuration);
        if (codecs.length > 0) {
            mediaInfo.mimeType += '; codecs="' + codecs.join(',') + '"';
        }
        let bitrateMap = [];
        for (let i = 0; i < maxDuration; i++) {
            let size = 0;
            if (mediaInfo.hasVideo) {
                size += bitrateMapTrack.video[i];
            }
            if (mediaInfo.hasAudio) {
                size += bitrateMapTrack.audio[i];
            }
            bitrateMap[i] = size * 8 / 1e3;
        }
        mediaInfo.bitrateMap = bitrateMap;
        chunkMap.sort(function (a, b) {
            return a.offset - b.offset;
        });
        this._chunkMap = chunkMap;
        this._mediaInfo = mediaInfo;
        if (mediaInfo.isComplete())
            this._onMediaInfo(mediaInfo);
        Log.v(this.TAG, 'Parsed moov box, hasVideo: ' + mediaInfo.hasVideo + ' hasAudio: ' + mediaInfo.hasAudio);
    }

    bindDataSource(loader) {
        loader.onDataArrival = this.parseChunks.bind(this);
        return this;
    }

    // prototype: function(type: string, metadata: any): void
    get onTrackMetadata() {
        return this._onTrackMetadata;
    }

    set onTrackMetadata(callback) {
        this._onTrackMetadata = callback;
    }

    // prototype: function(mediaInfo: MediaInfo): void
    get onMediaInfo() {
        return this._onMediaInfo;
    }

    set onMediaInfo(callback) {
        this._onMediaInfo = callback;
    }

    // prototype: function(type: number, info: string): void
    get onError() {
        return this._onError;
    }

    set onError(callback) {
        this._onError = callback;
    }

    // prototype: function(videoTrack: any, audioTrack: any): void
    get onDataAvailable() {
        return this._onDataAvailable;
    }

    set onDataAvailable(callback) {
        this._onDataAvailable = callback;
    }

    // timestamp base for output samples, must be in milliseconds
    get timestampBase() {
        return this._timestampBase;
    }

    set timestampBase(base) {
        this._timestampBase = base;
    }

    get overridedDuration() {
        return this._duration;
    }

    // Force-override media duration. Must be in milliseconds, int32
    set overridedDuration(duration) {
        this._durationOverrided = true;
        this._duration = duration;
        this._mediaInfo.duration = duration;
    }

    resetMediaInfo() {
        this._mediaInfo = new MediaInfo();
    }

    _isInitialMetadataDispatched() {
        if (this._hasAudio && this._hasVideo) {  // both audio & video
            return this._audioInitialMetadataDispatched && this._videoInitialMetadataDispatched;
        }
        if (this._hasAudio && !this._hasVideo) {  // audio only
            return this._audioInitialMetadataDispatched;
        }
        if (!this._hasAudio && this._hasVideo) {  // video only
            return this._videoInitialMetadataDispatched;
        }
        return false;
    }

    // function parseChunks(chunk: ArrayBuffer, byteStart: number): number;
    parseChunks(chunk, byteStart) {
        if (!this._onError || !this._onMediaInfo || !this._onTrackMetadata || !this._onDataAvailable) {
            throw new IllegalStateException('Flv: onError & onMediaInfo & onTrackMetadata & onDataAvailable callback must be specified');
        }

        let offset = 0;
        let le = this._littleEndian;

        if (byteStart === 0) {  // buffer with header
            let probeData = MP4Demuxer.probe(chunk);
            offset = probeData.dataOffset;
            if (!probeData.enoughData) {
                return 0;
            }
        }


        if (this._firstParse) {  // parse moov box
            this._firstParse = false;
            if (byteStart + offset !== this._dataOffset) {
                Log.w(this.TAG, 'First time parsing but chunk byteStart invalid!');
            }

            let uintarr = new Uint8Array(chunk);
            let moov = boxInfo(uintarr, offset);
            //moov still not finished, wait for it
            if (!moov.fullyLoaded) {
                this._firstParse = true;
                return 0;
            }
            let moovData = new Uint8Array(chunk, byteStart + offset, moov.size);
            this._parseMoov(moovData);
            offset += moov.size;
        }

        while (offset < chunk.byteLength) {
            this._dispatch = true;

            let v = new Uint8Array(chunk, offset);

            if (offset + 8 > chunk.byteLength) {
                // data not enough for parsing box size
                break;
            }

            let chunkMap = this._chunkMap;
            if (this._mdatEnd > byteStart + offset) {
                //find the chunk
                let sampleOffset = byteStart + offset;
                let dataChunk = chunkMap[0];
                for (let i = 1; i < chunkMap.length; i++) {
                    dataChunk = chunkMap[i];
                    if (sampleOffset < dataChunk.offset) {
                        dataChunk = chunkMap[i - 1];
                        break;
                    }
                }

                //find out which sample
                sampleOffset -= dataChunk.offset;
                let sample;
                for (let i = 0; i < dataChunk.samples.length; i++) {
                    if (sampleOffset == 0) {
                        sample = dataChunk.samples[i];
                        break;
                    }
                    sampleOffset -= dataChunk.samples[i].size;
                }

                if (!sample) {
                    break;
                }

                let sampleSize;
                if (dataChunk.type == 'video') {
                    sampleSize = sample.size;
                    if (offset + sampleSize > chunk.byteLength) {
                        break;
                    }
                    this._parseAVCVideoData(chunk, offset, sampleSize, sample.ts, byteStart + offset, sample.isKeyframe, sample.cts, sample.duration);
                } else if (dataChunk.type == 'audio') {
                    sampleSize = sample.size;
                    if (offset + sampleSize > chunk.byteLength) {
                        break;
                    }
                    let track = this._audioTrack;
                    let dts = this._timestampBase / 1e3 * this._audioMetadata.timescale + sample.ts;
                    let aacSample = { unit: v.subarray(0, sampleSize), dts: dts, pts: dts };
                    track.samples.push(aacSample);
                    track.length += aacSample.unit.length;
                }

                offset += sampleSize;
            } else {
                let box = boxInfo(v, 0);
                if (box.name == 'mdat') {
                    this._mdatEnd = byteStart + offset + box.size - 8;
                    offset += box.headSize;
                } else {
                    if (box.fullyLoaded) {
                        //not mdat box, skip
                        offset += box.size;
                    } else {
                        //not mdat box, not fully loaded, break out
                        break;
                    }
                }
            }
        }

        // dispatch parsed frames to consumer (typically, the remuxer)
        if (this._isInitialMetadataDispatched()) {
            if (this._dispatch && (this._audioTrack.length || this._videoTrack.length)) {
                this._onDataAvailable(this._audioTrack, this._videoTrack);
            }
        }

        return offset;  // consumed bytes, just equals latest offset index
    }

    _parseAVCVideoData(arrayBuffer, dataOffset, dataSize, tagTimestamp, tagPosition, frameType, cts, duration) {
        let le = this._littleEndian;
        let v = new DataView(arrayBuffer, dataOffset, dataSize);

        let units = [], length = 0;

        let offset = 0;
        const lengthSize = this._naluLengthSize;
        let dts = this._timestampBase / 1e3 * this._videoMetadata.timescale + tagTimestamp;
        let keyframe = (frameType === 1);  // from FLV Frame Type constants

        while (offset < dataSize) {
            if (offset + 4 >= dataSize) {
                Log.w(this.TAG, `Malformed Nalu near timestamp ${dts}, offset = ${offset}, dataSize = ${dataSize}`);
                break;  // data not enough for next Nalu
            }
            // Nalu with length-header (AVC1)
            let naluSize = v.getUint32(offset, !le);  // Big-Endian read
            if (lengthSize === 3) {
                naluSize >>>= 8;
            }
            if (naluSize > dataSize - lengthSize) {
                Log.w(this.TAG, `Malformed Nalus near timestamp ${dts}, NaluSize > DataSize!`);
                return;
            }

            let unitType = v.getUint8(offset + lengthSize) & 0x1F;

            if (unitType === 5) {  // IDR
                keyframe = true;
            }

            let data = new Uint8Array(arrayBuffer, dataOffset + offset, lengthSize + naluSize);
            let unit = { type: unitType, data: data };
            units.push(unit);
            length += data.byteLength;

            offset += lengthSize + naluSize;
        }

        if (units.length) {
            let track = this._videoTrack;
            let avcSample = {
                units: units,
                length: length,
                duration: duration,
                isKeyframe: keyframe,
                dts: dts,
                cts: cts,
                pts: (dts + cts)
            };
            if (keyframe) {
                avcSample.fileposition = tagPosition;
            }
            track.samples.push(avcSample);
            track.length += length;
        }
    }

}

export default MP4Demuxer;