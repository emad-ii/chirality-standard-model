import {execFileSync} from 'node:child_process';
import {writeFileSync,readFileSync,mkdirSync} from 'node:fs';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
const path='outputs/one-survivor-pilot.mp4';
const probe=JSON.parse(execFileSync('ffprobe',['-v','error','-show_streams','-show_format','-of','json',path],{encoding:'utf8'}));
const stream=probe.streams.find(s=>s.codec_type==='video');
assert.equal(stream.width,1920);assert.equal(stream.height,1080);assert.equal(stream.r_frame_rate,'30/1');
assert(Math.abs(Number(probe.format.duration)-78)<.1);
assert.equal(probe.streams.filter(s=>s.codec_type==='audio').length,0);
mkdirSync('outputs/rendered-frames',{recursive:true});
const samples=[.5,10,29,44,47.5,53,54,57.5,69,76];
const frames=samples.map(time=>{
  const output=`outputs/rendered-frames/at-${time}s.png`;
  execFileSync('ffmpeg',['-v','error','-y','-ss',String(time),'-i',path,'-frames:v','1',output]);
  return {time,path:output,sha256:createHash('sha256').update(readFileSync(output)).digest('hex')};
});
assert.equal(new Set(frames.map(f=>f.sha256)).size,frames.length,'All sampled frames must differ; this is not a substitute for visual motion review.');
const result={passed:true,video:{path,width:stream.width,height:stream.height,fps:stream.r_frame_rate,duration:probe.format.duration,codec:stream.codec_name,audio:'intentionally silent'},frames,
  scope:'Container properties and decoded frame diversity. Human visual judgement and final narrated-film QA remain separate.'};
writeFileSync('outputs/export-check.json',JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result.video,null,2));
console.log('Export checks passed; 10 decoded frames saved for inspection.');
