import {mkdirSync,writeFileSync,readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {captions,revision,duration} from '../data.mjs';
const stamp=t=>`${String(Math.floor(t/3600)).padStart(2,'0')}:${String(Math.floor(t/60)%60).padStart(2,'0')}:${String(Math.floor(t)%60).padStart(2,'0')}.000`;
mkdirSync('outputs',{recursive:true});
writeFileSync('outputs/one-survivor-pilot.vtt','WEBVTT\n\n'+captions.map(([a,b,text])=>`${stamp(a)} --> ${stamp(b)}\n${text}\n`).join('\n'));
const files=['index.html','film.css','film.mjs','data.mjs','package-lock.json'];
writeFileSync('outputs/source-manifest.json',JSON.stringify({
  title:'One survivor — silent visual pilot',status:'pilot; not the main narrated film',durationSeconds:duration,
  paperRevision:revision,render:{width:1920,height:1080,fps:30,workers:1,hyperframes:'0.8.30',audio:'none'},
  verificationScope:'Presentation data, representation arithmetic and illustration geometry; not a proof of the full classification.',
  sourceFiles:files.map(path=>({path,sha256:createHash('sha256').update(readFileSync(path)).digest('hex')})),
},null,2)+'\n');
console.log('Exported captions and source manifest.');
