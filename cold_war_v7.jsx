import { useEffect, useRef, useState } from "react";

const GLOBE_R       = 130;
const FLY_ALT       = 52;     // single altitude — missiles AND interceptors fly here
const MISSILE_SPEED = 0.18;
const ICEPT_SPEED   = 0.1854; // 0.18 * 1.03
const RADAR_RANGE   = 115;
// Wave system defined in init
const DETECT_DELAY  = 700;
const HIT_DIST      = 3.5;    // must physically collide — tight radius
const SITE_HIT_DIST = 12;     // missile hits bear site on surface
const MAX_HP        = 3;
const REPAIR_EVERY  = 3;
// Evasion
const CURVE_INTERVAL = 100;   // frames between starting a new deviation curve
const CURVE_CHANCE   = 0.40;  // probability of beginning a curve
const CURVE_RATE     = 0.018; // radians per frame — constant turn applied every frame
const EVASION_BUDGET  = 3;     // max number of evasion maneuvers per missile lifetime
const CURVE_FRAMES   = 110;
const ICEPT_MAX_AGE  = 550; // frames before interceptor runs out of fuel (~9s)
const MAX_ICEPT_PER_MISSILE = 2; // max interceptors globally targeting same missile   // how many frames the curve lasts

function App({ onGameOver, onExit }) {
  const mountRef = useRef(null);
  const [stats, setStats]   = useState({ l:0, i:0, h:0, a:0, w:0, il:0 });
  const [gameOver, setGameOver] = useState(null);
  const [siteHp, setSiteHp] = useState([3,3,3,3,3]);
  const [evMsg, setEvMsg]   = useState(null);
  const [paused, setPaused] = useState(false);
  const [confirmExit, setConfirmExit] = useState(false);
  const pausedRef     = useRef(false);
  const animIdRef     = useRef(null);
  const waveTimerRef  = useRef(null);
  const gameOverFired = useRef(false);

  useEffect(() => {
    let THREE;
    let scene, camera, renderer, G;
    let launched=0, intercepted=0, impacts=0, interceptSinceRepair=0, iceptLaunched=0;
    const missiles=[], icepts=[], exps=[], beams=[];
    const bearBases=[], bearRadars=[], penguinRadars=[];
    const detectionLog = new Set();
    let midCounter = 0;
    const siteHpRef = [3,3,3,3,3];

    function showEv(txt,col,sub=""){setEvMsg({txt,col,sub});setTimeout(()=>setEvMsg(null),2000);}

    function ll2v(lat,lng,r=GLOBE_R){
      const phi=(90-lat)*Math.PI/180,th=(lng+180)*Math.PI/180;
      return new THREE.Vector3(-r*Math.sin(phi)*Math.cos(th),r*Math.cos(phi),r*Math.sin(phi)*Math.sin(th));
    }

    // Project pos onto sphere at given altitude
    function onSphere(pos,alt){return pos.clone().normalize().multiplyScalar(GLOBE_R+alt);}

    // Move `pos` in direction `vel` by `speed`, stay on sphere at `alt`
    // Returns new {pos, vel}
    function moveOnSphere(pos, vel, speed, alt){
      const next = pos.clone().addScaledVector(vel, speed);
      const newPos = onSphere(next, alt);
      const normal = newPos.clone().normalize();
      let tangent = vel.clone().sub(normal.clone().multiplyScalar(normal.dot(vel)));
      // Guard: if tangent is near-zero (vel ~radial), pick a perpendicular direction
      if(tangent.length() < 0.001){
        const perp = Math.abs(normal.x) < 0.9 ? new THREE.Vector3(1,0,0) : new THREE.Vector3(0,1,0);
        tangent = perp.sub(normal.clone().multiplyScalar(normal.dot(perp)));
      }
      const newVel = tangent.normalize();
      // Final NaN guard
      if(isNaN(newVel.x)) return {pos, vel};
      return {pos: newPos, vel: newVel};
    }

    // Steer vel toward a target point (on sphere), with max turn rate
    function steerVel(pos, vel, targetPos, maxTurn){
      const desired = targetPos.clone().sub(pos).normalize();
      const normal  = pos.clone().normalize();
      // Project desired onto tangent plane
      const tangent = desired.sub(normal.clone().multiplyScalar(normal.dot(desired))).normalize();
      if(tangent.length() < 0.001) return vel;
      // Slerp toward tangent
      const angle = Math.min(maxTurn, vel.angleTo(tangent));
      if(angle < 0.0001) return tangent.clone();
      const axis = new THREE.Vector3().crossVectors(vel, tangent).normalize();
      if(axis.length() < 0.001) return tangent.clone();
      return vel.clone().applyAxisAngle(axis, angle).normalize();
    }

    // Random tangent vector perpendicular to normal
    function randomTangent(pos){
      const n = pos.clone().normalize();
      const rand = new THREE.Vector3(Math.random()-0.5, Math.random()-0.5, Math.random()-0.5).normalize();
      return rand.sub(n.clone().multiplyScalar(n.dot(rand))).normalize();
    }

    // Intercept prediction: iterate to find where missile will be when interceptor arrives
    // Now uses missile velocity for better prediction
    // Radar track: only what radar can observe — position + velocity direction
    // Updated each time radar sweeps past missile (every RADAR_UPDATE_FRAMES)
    // Interceptor uses this stale data, NOT live missile object
    // Intercept prediction — robust to stale radar data and evasion maneuvers
    // Simple lead pursuit: project missile forward along observed velocity,
    // but blend toward direct pursuit as uncertainty grows (older track = aim closer to current pos)
    function computeIntercept(ipos, ivel, track){
      const dist = ipos.distanceTo(track.pos);
      if(dist < 0.001) return track.pos.clone();

      // How stale is the track? (0=fresh, 1=very stale)
      const staleness = Math.min(1, track.age / 90);

      // Lead time estimate — how many frames until we reach the missile
      const leadFrames = Math.min(dist / ICEPT_SPEED, 70);

      // Project missile forward along its observed velocity
      // Staleness reduces lead — when data is old, aim closer to last known position
      const lead = leadFrames * (1 - staleness * 0.7);
      const aimed = track.pos.clone()
        .addScaledVector(track.vel, lead * MISSILE_SPEED);

      // Preserve missile's observed altitude — don't guess about arc
      aimed.normalize().multiplyScalar(track.pos.length());
      return aimed;
    }

    // Interceptor steering: true 3D movement toward aim point
    // No altitude snapping — moves freely in 3D space at exactly ICEPT_SPEED
    // Only prevents going underground (below GLOBE_R + 1)
    const ICEPT_MAX_TURN = 0.06; // wider turn rate for 3D free movement
    function steerInterceptor(pos, vel, aim, speed){
      // Desired direction in full 3D (not projected to tangent plane)
      const toAim = aim.clone().sub(pos);
      const dist = toAim.length();
      if(dist < 0.001) return {pos, vel};
      const desired = toAim.normalize();
      // Clamp turn rate — interceptor can't instantly reverse
      const angle = Math.min(ICEPT_MAX_TURN, vel.angleTo(desired));
      let newVel;
      if(angle < 0.0001){ newVel = desired.clone(); }
      else {
        const axis = new THREE.Vector3().crossVectors(vel, desired);
        if(axis.length() < 0.001){ newVel = vel.clone(); }
        else { newVel = vel.clone().applyAxisAngle(axis.normalize(), angle).normalize(); }
      }
      if(isNaN(newVel.x)) newVel = vel.clone();
      // Move in 3D at exactly `speed` units per frame
      let newPos = pos.clone().addScaledVector(newVel, Math.min(speed, dist));
      // Only constraint: don't go underground
      if(newPos.length() < GLOBE_R + 1){
        newPos = newPos.normalize().multiplyScalar(GLOBE_R + 1);
      }
      return {pos: newPos, vel: newVel};
    }

    const PENGUINS=[{lat:-76,lng:-45},{lat:-80,lng:60},{lat:-72,lng:160},{lat:-78,lng:-120},{lat:-74,lng:-10}].map(s=>({...s,vec:null}));
    const BEARS=[{lat:78,lng:0},{lat:76,lng:90},{lat:80,lng:-60},{lat:74,lng:160},{lat:82,lng:-150}].map(s=>({...s,vec:null}));

    const script = document.createElement("script");
    script.src = "https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js";
    script.onload = () => { THREE=window.THREE; init(); };
    document.head.appendChild(script);

    function init(){
      const W=mountRef.current.clientWidth, H=mountRef.current.clientHeight;
      renderer=new THREE.WebGLRenderer({antialias:true,powerPreference:"high-performance"});
      renderer.setPixelRatio(Math.min(window.devicePixelRatio,3));
      renderer.setSize(W,H); renderer.setClearColor(0x000000);
      mountRef.current.appendChild(renderer.domElement);
      scene=new THREE.Scene();
      camera=new THREE.PerspectiveCamera(44,W/H,0.5,4000);
      camera.position.set(0,60,340); camera.lookAt(0,0,0);

      // Stars
      const sp=new Float32Array(3000);
      for(let i=0;i<1000;i++){const th=Math.random()*Math.PI*2,ph=Math.acos(2*Math.random()-1),r=750+Math.random()*250;sp[i*3]=r*Math.sin(ph)*Math.cos(th);sp[i*3+1]=r*Math.cos(ph);sp[i*3+2]=r*Math.sin(ph)*Math.sin(th);}
      const sg=new THREE.BufferGeometry();sg.setAttribute("position",new THREE.BufferAttribute(sp,3));
      scene.add(new THREE.Points(sg,new THREE.PointsMaterial({color:0xffffff,size:1.1})));

      G=new THREE.Group();scene.add(G);
      G.add(new THREE.Mesh(new THREE.SphereGeometry(GLOBE_R,96,96),new THREE.MeshPhongMaterial({color:0x010f05,emissive:0x001a08,shininess:18})));
      G.add(new THREE.Mesh(new THREE.SphereGeometry(GLOBE_R+4,24,24),new THREE.MeshPhongMaterial({color:0x003311,transparent:true,opacity:0.06,side:THREE.BackSide})));
      scene.add(new THREE.AmbientLight(0x112211,0.55));
      const sun=new THREE.DirectionalLight(0x55ee88,1.0);sun.position.set(350,180,120);scene.add(sun);
      const iceMat=new THREE.MeshPhongMaterial({color:0x99ffcc,transparent:true,opacity:0.3});
      G.add(new THREE.Mesh(new THREE.SphereGeometry(GLOBE_R+0.4,32,16,0,Math.PI*2,0,0.25),iceMat));
      G.add(new THREE.Mesh(new THREE.SphereGeometry(GLOBE_R+0.4,32,16,0,Math.PI*2,2.89,0.25),iceMat));

      // Borders
      const bMat=new THREE.LineBasicMaterial({color:0x00cc44,transparent:true,opacity:0.85});
      function addLine(c){if(c.length<2)return;G.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints(c.map(([lng,lat])=>ll2v(lat,lng,GLOBE_R+0.35))),bMat));}
      function dg(g){if(!g)return;if(g.type==="Polygon")g.coordinates.forEach(addLine);else if(g.type==="MultiPolygon")g.coordinates.forEach(p=>p.forEach(addLine));else if(g.type==="LineString")addLine(g.coordinates);else if(g.type==="MultiLineString")g.coordinates.forEach(addLine);}
      (async()=>{
        try{
          await new Promise((res,rej)=>{
            const s=document.createElement("script");
            s.src="https://cdnjs.cloudflare.com/ajax/libs/topojson/3.0.2/topojson.min.js";
            s.onload=res;s.onerror=rej;document.head.appendChild(s);
          });
          const w=await(await fetch("https://cdn.jsdelivr.net/npm/world-atlas@2/countries-50m.json")).json();
          // Draw every ring of every country polygon — fills all coastlines + borders
          const countries=window.topojson.feature(w,w.objects.countries);
          const borderMat=new THREE.LineBasicMaterial({color:0x22c55e,transparent:true,opacity:0.85});
          countries.features.forEach(f=>{
            const geoms=f.geometry.type==="Polygon"?[f.geometry.coordinates]:f.geometry.coordinates;
            geoms.forEach(poly=>poly.forEach(ring=>{
              const pts=ring.map(([lng,lat])=>ll2v(lat,lng,GLOBE_R+0.35));
              G.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints(pts),borderMat));
            }));
          });
        }catch(_){
          // Fallback grid
          const gm=new THREE.LineBasicMaterial({color:0x00aa33,transparent:true,opacity:0.25});
          for(let la=-80;la<=80;la+=20){const pts=[];for(let ln=-180;ln<=180;ln+=4)pts.push(ll2v(la,ln,GLOBE_R+0.4));G.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints(pts),gm));}
          for(let ln=-180;ln<=180;ln+=20){const pts=[];for(let la=-80;la<=80;la+=3)pts.push(ll2v(la,ln,GLOBE_R+0.4));G.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints(pts),gm));}
        }

        // Arctic circle (66.5°N) — bright teal
        const arcticMat=new THREE.LineBasicMaterial({color:0x22d3ee,transparent:true,opacity:0.6});
        const arcticPts=[];
        for(let ln=-180;ln<=180;ln+=2) arcticPts.push(ll2v(66.5,ln,GLOBE_R+0.5));
        G.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints(arcticPts),arcticMat));

        // Antarctic circle (66.5°S) — lighter blue-white
        const antMat=new THREE.LineBasicMaterial({color:0x7dd3fc,transparent:true,opacity:0.6});
        const antPts=[];
        for(let ln=-180;ln<=180;ln+=2) antPts.push(ll2v(-66.5,ln,GLOBE_R+0.5));
        G.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints(antPts),antMat));

        // South Pole landmass outline — rough circle at ~70°S to show Antarctica
        const antarcticaMat=new THREE.LineBasicMaterial({color:0xbae6fd,transparent:true,opacity:0.45});
        for(let lat of [-70,-75,-80]){
          const pts=[];
          for(let ln=-180;ln<=180;ln+=2) pts.push(ll2v(lat,ln,GLOBE_R+0.5));
          G.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints(pts),antarcticaMat));
        }

        // North Pole — concentric rings to show Arctic ocean extent
        const northMat=new THREE.LineBasicMaterial({color:0x67e8f9,transparent:true,opacity:0.35});
        for(let lat of [75,80,85]){
          const pts=[];
          for(let ln=-180;ln<=180;ln+=2) pts.push(ll2v(lat,ln,GLOBE_R+0.5));
          G.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints(pts),northMat));
        }
      })();

      // Sprites
      const sc={};
      function mkSpr(e,sz){if(!sc[e]){const c=document.createElement("canvas");c.width=c.height=96;const ctx=c.getContext("2d");ctx.font="68px serif";ctx.textAlign=ctx.textBaseline="middle";ctx.fillText(e,48,52);sc[e]=new THREE.CanvasTexture(c);}const s=new THREE.Sprite(new THREE.SpriteMaterial({map:sc[e],transparent:true}));s.scale.set(sz,sz,1);return s;}
      PENGUINS.forEach(s=>{s.vec=ll2v(s.lat,s.lng);const sp=mkSpr("🐧",18);sp.position.copy(ll2v(s.lat,s.lng,GLOBE_R+7));G.add(sp);});

      BEARS.forEach((s,bi)=>{
        s.vec=ll2v(s.lat,s.lng);
        const sp=mkSpr("🐻‍❄️",18);sp.position.copy(ll2v(s.lat,s.lng,GLOBE_R+7));G.add(sp);
        const n=s.vec.clone().normalize();
        const glow=new THREE.Mesh(new THREE.SphereGeometry(4.5,10,10),new THREE.MeshBasicMaterial({color:0x00ff88,transparent:true,opacity:0.9}));
        glow.position.copy(n.clone().multiplyScalar(GLOBE_R+1.5));G.add(glow);
        const halo=new THREE.Mesh(new THREE.SphereGeometry(7,10,10),new THREE.MeshBasicMaterial({color:0x00ff88,transparent:true,opacity:0.15}));
        halo.position.copy(glow.position);G.add(halo);
        const hpDots=[];
        let up=new THREE.Vector3(0,1,0);if(Math.abs(n.dot(up))>0.9)up.set(1,0,0);
        const r2=new THREE.Vector3().crossVectors(n,up).normalize();
        const u2=new THREE.Vector3().crossVectors(r2,n).normalize();
        for(let k=0;k<MAX_HP;k++){
          const ang=k/MAX_HP*Math.PI*2;
          const dot=new THREE.Mesh(new THREE.SphereGeometry(1.2,6,6),new THREE.MeshBasicMaterial({color:0x00ff88,transparent:true,opacity:1}));
          dot.position.copy(n.clone().multiplyScalar(GLOBE_R+2).add(r2.clone().multiplyScalar(Math.cos(ang)*9)).add(u2.clone().multiplyScalar(Math.sin(ang)*9)));
          G.add(dot);hpDots.push(dot);
        }
        // Pulse rings: 3 expanding rings that ripple outward from base
        // Sonar-ping style rings: each starts tiny, expands to RADAR_RANGE, fades out
        // Geometry at scale=1 is full RADAR_RANGE size — we scale from 0.01→1
        const pulseRings=[];
        for(let k=0;k<3;k++){
          const ring=new THREE.Mesh(
            new THREE.RingGeometry(RADAR_RANGE-1.5, RADAR_RANGE, 64),
            new THREE.MeshBasicMaterial({color:0x00ff88,transparent:true,opacity:0,side:THREE.DoubleSide})
          );
          ring.position.copy(n.clone().multiplyScalar(GLOBE_R+0.5));
          ring.quaternion.setFromUnitVectors(new THREE.Vector3(0,0,1),n);
          G.add(ring);
          // Stagger starting age so rings are evenly spaced in cycle
          pulseRings.push({mesh:ring, age: k*(100/3)});
        }
        bearBases.push({glow,halo,phase:Math.random()*Math.PI*2,hpDots});
        bearRadars.push({pulseRings,normal:n,bi,pulseColor:0x00ff88});
      });

      function mkRings(sv,color){
        const n=sv.clone().normalize(),bp=n.clone().multiplyScalar(GLOBE_R+1.2);
        let up=new THREE.Vector3(0,1,0);if(Math.abs(n.dot(up))>0.9)up.set(1,0,0);
        const r2=new THREE.Vector3().crossVectors(n,up).normalize();
        const u2=new THREE.Vector3().crossVectors(r2,n).normalize();
        const rings=[];
        for(let i=0;i<3;i++){const pts=[];for(let j=0;j<=48;j++){const a=j/48*Math.PI*2,r=14;const wp=new THREE.Vector3().addScaledVector(r2,Math.cos(a)*r).addScaledVector(u2,Math.sin(a)*r).add(bp);wp.normalize().multiplyScalar(GLOBE_R+1.5);pts.push(wp.clone());}const mat=new THREE.LineBasicMaterial({color,transparent:true,opacity:0});const line=new THREE.Line(new THREE.BufferGeometry().setFromPoints(pts),mat);G.add(line);rings.push({line,mat,t:i/3});}
        return{rings,update(){this.rings.forEach(r=>{r.t+=0.012;if(r.t>1)r.t-=1;const s=0.3+r.t*1.7;r.line.scale.set(s,s,s);r.mat.opacity=r.t<0.1?r.t/0.1*0.8:Math.max(0,(1-r.t)*0.8);});},flash(){this.rings.forEach(r=>{r.mat.opacity=1;r.t=0.05;});}};
      }
      PENGUINS.forEach(s=>{const g=new THREE.Mesh(new THREE.SphereGeometry(3.5,8,8),new THREE.MeshBasicMaterial({color:0xff3300,transparent:true,opacity:0.85}));g.position.copy(s.vec.clone().normalize().multiplyScalar(GLOBE_R+1.5));G.add(g);penguinRadars.push(mkRings(s.vec,0xff4400));});

      const TL=28;
      function mkTrail(color,op=0.9){const pts=[],mat=new THREE.LineBasicMaterial({color,transparent:true,opacity:op});const geo=new THREE.BufferGeometry();const line=new THREE.Line(geo,mat);G.add(line);return{pts,line,geo,mat,add(v){pts.push(v.clone());if(pts.length>TL)pts.shift();if(pts.length>=2){geo.setFromPoints(pts);mat.opacity=Math.min(op,pts.length/TL);}},dispose(){G.remove(line);geo.dispose();}};}

      const EG=new THREE.SphereGeometry(1,4,4);
      function explode(pos,color,sz=1){const grp=new THREE.Group();grp.position.copy(pos);const parts=[];for(let i=0;i<14;i++){const m=new THREE.Mesh(EG,new THREE.MeshBasicMaterial({color,transparent:true,opacity:1}));m.scale.setScalar(sz*0.8);const th=Math.random()*Math.PI*2,ph=Math.acos(2*Math.random()-1),spd=(0.5+Math.random()*1.3)*sz;const vel=new THREE.Vector3(Math.sin(ph)*Math.cos(th),Math.cos(ph),Math.sin(ph)*Math.sin(th)).multiplyScalar(spd);parts.push({m,vel});grp.add(m);}const fl=new THREE.Mesh(new THREE.SphereGeometry(5*sz,6,6),new THREE.MeshBasicMaterial({color:0xffffff,transparent:true,opacity:0.9}));grp.add(fl);G.add(grp);exps.push({grp,parts,fl,age:0,max:45,sz});}

      function spawnBeam(vec){const mat=new THREE.LineBasicMaterial({color:0x00ffcc,transparent:true,opacity:1});const line=new THREE.Line(new THREE.BufferGeometry().setFromPoints([vec.clone().normalize().multiplyScalar(GLOBE_R+2),vec.clone().normalize().multiplyScalar(GLOBE_R+32)]),mat);G.add(line);beams.push({line,mat,age:0,max:18});}

      function updateSiteVisual(bi){
        const hp=siteHpRef[bi];
        const colors=[0x00ff88,0x00ff88,0xffcc00,0xff4400];
        const col=hp>0?colors[MAX_HP-hp]:0x333333;
        const b=bearBases[bi];
        b.glow.material.color.setHex(col);b.halo.material.color.setHex(col);
        bearRadars[bi].pulseColor=col;
        bearRadars[bi].pulseRings.forEach(r=>r.mesh.material.color.setHex(col));
        b.hpDots.forEach((d,k)=>{d.material.color.setHex(k<hp?col:0x222222);d.material.opacity=k<hp?1:0.2;});
        setSiteHp([...siteHpRef]);
      }

      function tryRepair(){
        let worst=-1,worstHp=MAX_HP;
        siteHpRef.forEach((hp,i)=>{if(hp>0&&hp<worstHp){worstHp=hp;worst=i;}});
        if(worst>=0){siteHpRef[worst]=Math.min(MAX_HP,siteHpRef[worst]+1);updateSiteVisual(worst);showEv(`🔧 BASE ${worst+1} REPAIRED`,"#4ade80",`HP: ${siteHpRef[worst]}/${MAX_HP}`);}
      }

      // ── MISSILE (velocity-steered, evasive) ───────────────
      function mkMissileMesh(){
        const grp = new THREE.Group();
        const mat = new THREE.MeshPhongMaterial({color:0xff2200, emissive:0x880000, shininess:40});
        // Body
        const body = new THREE.Mesh(new THREE.CylinderGeometry(0.8,0.8,5,8), mat);
        grp.add(body);
        // Round nose — hemisphere (sphere clipped to top half via scale)
        const nose = new THREE.Mesh(new THREE.SphereGeometry(0.8,8,8,0,Math.PI*2,0,Math.PI*0.55), mat);
        nose.position.y = 2.6;
        grp.add(nose);
        // Fins
        const finMat = new THREE.MeshPhongMaterial({color:0xcc1100,emissive:0x440000});
        for(let i=0;i<4;i++){
          const fin = new THREE.Mesh(new THREE.BoxGeometry(0.2,2,1.2), finMat);
          fin.position.y = -2;
          fin.rotation.y = i*Math.PI/2;
          fin.position.x = Math.cos(i*Math.PI/2)*1.0;
          fin.position.z = Math.sin(i*Math.PI/2)*1.0;
          grp.add(fin);
        }
        return grp;
      }
      function mkMissile(site){
        const aliveBears=BEARS.filter((_,i)=>siteHpRef[i]>0);
        const target=aliveBears.length>0?aliveBears[Math.floor(Math.random()*aliveBears.length)]:BEARS[Math.floor(Math.random()*BEARS.length)];
        const targetBearIdx=BEARS.indexOf(target);
        const startPos=onSphere(site.vec, 1.5); // ground launch
        // Noisy target — guidance drift, CEP error like real ICBMs
        const noiseDir = new THREE.Vector3(Math.random()-0.5,Math.random()-0.5,Math.random()-0.5).normalize();
        const noiseMag = 4 + Math.random()*8; // 4-12 unit CEP error
        const targetPos = target.vec.clone().addScaledVector(noiseDir, noiseMag).normalize().multiplyScalar(GLOBE_R);
        // Initial velocity: point toward target
        const initDir=targetPos.clone().sub(startPos);
        const n=startPos.clone().normalize();
        const tangent=initDir.sub(n.clone().multiplyScalar(n.dot(initDir))).normalize();
        const mesh=mkMissileMesh();
        const trail=mkTrail(0xff5500,0.8);
        mesh.position.copy(startPos);G.add(mesh);
        launched++;setStats(s=>({...s,l:launched}));
        return{
          id:midCounter++,
          pos:startPos.clone(),
          vel:tangent.clone(),
          targetPos: targetPos.clone(),
          targetBearIdx,
          dead:false, mesh, trail,
          frameCount:0,
          startNorm: startPos.clone().normalize(),
          targetNorm: targetPos.clone().normalize(),
          curving:false,
          curveFrames:0,
          curveAxis:new THREE.Vector3(0,1,0),
          threatRange:false,
          evasionBudget: EVASION_BUDGET, // fuel budget for maneuvers
          distToTarget(){ return this.pos.distanceTo(this.targetPos); }
        };
      }

      // ── INTERCEPTOR ────────────────────────────────────────
      const IG=new THREE.SphereGeometry(1.3,5,5);
      function mkIcept(bearSite, target, bi){
        iceptLaunched++;
        setStats(s=>({...s,il:iceptLaunched}));
        const mesh = new THREE.Mesh(IG, new THREE.MeshBasicMaterial({color:0x00ddff}));
        const trail = mkTrail(0x00aaff, 0.7);
        const launchPos = bearSite.vec.clone().normalize().multiplyScalar(GLOBE_R + 1.5);
        mesh.position.copy(launchPos); G.add(mesh);
        spawnBeam(bearSite.vec);
        const track = { pos: target.pos.clone(), vel: target.vel.clone() };
        // Initial velocity in true 3D toward missile — no tangent projection
        let initVel = target.pos.clone().sub(launchPos);
        if(initVel.length() < 0.001) initVel = new THREE.Vector3(0,1,0);
        initVel.normalize();
        return { target, track, dead:false, pos:launchPos.clone(), vel:initVel.clone(),
                 mesh, trail, trackAge:0, bearIdx:bi, age:0 };
      }

      const MAX_ICEPT_PER_SITE = 4;
      function siteIceptCount(bi){ return icepts.filter(iv=>!iv.dead && iv.bearIdx===bi).length; }

      function checkRadar(){
        missiles.forEach(m=>{
          if(m.dead) return;
          BEARS.forEach((bear,bi)=>{
            if(siteHpRef[bi]<=0) return;
            const key=`${bi}-${m.id}`;
            if(detectionLog.has(key)) return;
            if(m.pos.distanceTo(bear.vec)<RADAR_RANGE){
              detectionLog.add(key);
              // Flash pulse rings on detection — reset ages to burst from center
              bearRadars[bi].pulseRings.forEach((r,k)=>{r.age=k*8;});
              setTimeout(()=>{
                if(m.dead || siteHpRef[bi]<=0) return;
                // Per-site limit
                if(siteIceptCount(bi) >= MAX_ICEPT_PER_SITE) return;
                // Global per-missile limit — don't pile on already-tracked missiles
                const alreadyTracking = icepts.filter(iv=>!iv.dead && iv.target===m).length;
                if(alreadyTracking >= MAX_ICEPT_PER_MISSILE) return;
                // Smart pick: find the missile in THIS site's radar range
                // that has the fewest interceptors assigned — may not be m
                const candidates = missiles.filter(cand=>
                  !cand.dead &&
                  cand.pos.distanceTo(bear.vec) < RADAR_RANGE &&
                  icepts.filter(iv=>!iv.dead && iv.target===cand).length < MAX_ICEPT_PER_MISSILE
                );
                if(candidates.length === 0) return;
                // Pick least-covered missile
                candidates.sort((a,b)=>
                  icepts.filter(iv=>!iv.dead&&iv.target===a).length -
                  icepts.filter(iv=>!iv.dead&&iv.target===b).length
                );
                icepts.push(mkIcept(bear, candidates[0], bi));
              }, DETECT_DELAY);
            }
          });
        });
      }

      function launch(){
        const si=Math.floor(Math.random()*PENGUINS.length);
        missiles.push(mkMissile(PENGUINS[si]));
        penguinRadars[si].flash();
      }
      // Wave system: escalating waves of missiles
      let waveNum = 0;
      let waveTimeout; waveTimerRef.current=null;

      function fireWave(){
        waveNum++;
        setStats(s=>({...s,w:waveNum}));
        // Consistent wave size: 8 missiles, +1 every 4 waves, caps at 20
        const waveSize = Math.min(20, 8 + Math.floor((waveNum - 1) / 4));
        const spread = 500; // ms between individual launches within wave
        for(let i = 0; i < waveSize; i++){
          setTimeout(launch, i * spread + Math.random() * 150);
        }
        // Gap between waves: steady 10s regardless of wave number
        const nextGap = 10000;
        if(waveNum >= 10){
          // Bears survived all 10 waves — bears win after last missiles clear
          waveTimeout = setTimeout(()=>{
            // Wait for remaining missiles to resolve (up to 30s), then declare bear victory
            const checkClear = setInterval(()=>{
              if(missiles.length === 0){
                clearInterval(checkClear);
                if(gameOverFired.current) return;
                gameOverFired.current = true;
                cancelAnimationFrame(animId);
                setTimeout(()=>{
                  const report = {
                    launched, impacts, iceptLaunched, intercepted,
                    waves: waveNum, timestamp: Date.now(), bearsWin: true
                  };
                  setGameOver(report);
                  onGameOver(report);
                }, 1500);
              }
            }, 500);
          }, nextGap + waveSize * spread);
        } else {
          waveTimeout = setTimeout(fireWave, nextGap + waveSize * spread);
        }
      }

      // First wave after a short delay
      waveTimeout = setTimeout(fireWave, 800); waveTimerRef.current=waveTimeout;

      // ── Controls ─────────────────────────────────────────
      // touch-action:none stops browser stealing touch events
      renderer.domElement.style.touchAction = "none";

      // Core rotate — quaternion, no gimbal lock
      function rotateGlobe(dx, dy){
        const s = 0.005;
        const axisY = new THREE.Vector3(0,1,0);
        const axisX = new THREE.Vector3(1,0,0).applyQuaternion(camera.quaternion);
        G.quaternion.premultiply(new THREE.Quaternion().setFromAxisAngle(axisY, dx*s));
        G.quaternion.premultiply(new THREE.Quaternion().setFromAxisAngle(axisX, dy*s));
      }

      // Inertia — velocity decays each frame for smooth coast after lift
      let velX=0, velY=0;
      const FRICTION = 0.88;

      let prev2=null, pinchD=null, pinchMid=null, pinchAngle=null;
      const cvs=renderer.domElement;

      // ── Touch ──────────────────────────────────────────
      cvs.addEventListener("touchstart",e=>{
        e.preventDefault();
        velX=0; velY=0; // kill inertia on new touch
        if(e.touches.length===1){
          prev2={x:e.touches[0].clientX,y:e.touches[0].clientY};
          pinchD=null; pinchMid=null;
        }
        if(e.touches.length===2){
          const dx2=e.touches[0].clientX-e.touches[1].clientX;
          const dy2=e.touches[0].clientY-e.touches[1].clientY;
          pinchD=Math.hypot(dx2,dy2);
          pinchMid={
            x:(e.touches[0].clientX+e.touches[1].clientX)/2,
            y:(e.touches[0].clientY+e.touches[1].clientY)/2
          };
          pinchAngle=Math.atan2(dy2,dx2); // track finger angle for twist
          prev2=null;
        }
      },{passive:false}); // passive:false so we can preventDefault

      cvs.addEventListener("touchmove",e=>{
        e.preventDefault();
        if(e.touches.length===1 && prev2){
          const dx=e.touches[0].clientX-prev2.x;
          const dy=e.touches[0].clientY-prev2.y;
          rotateGlobe(dx,dy);
          velX=dx; velY=dy; // store for inertia
          prev2={x:e.touches[0].clientX,y:e.touches[0].clientY};
        }
        if(e.touches.length===2 && pinchD!=null){
          const dx2=e.touches[0].clientX-e.touches[1].clientX;
          const dy2=e.touches[0].clientY-e.touches[1].clientY;
          const d=Math.hypot(dx2,dy2);
          const mid={
            x:(e.touches[0].clientX+e.touches[1].clientX)/2,
            y:(e.touches[0].clientY+e.touches[1].clientY)/2
          };
          // Pinch = zoom
          camera.position.z=Math.max(150,Math.min(900,camera.position.z*(pinchD/d)));
          // Midpoint drag = pan (no rotation)
          if(pinchMid){
            const dx=mid.x-pinchMid.x, dy=mid.y-pinchMid.y;
            const s = camera.position.z / 500;
            G.position.x = Math.max(-500, Math.min(500, G.position.x + dx*s));
            G.position.y = Math.max(-500, Math.min(500, G.position.y - dy*s));
          }
          // Twist = rotate around camera's look axis (clockwise/counterclockwise)
          if(pinchAngle!=null){
            const newAngle=Math.atan2(dy2,dx2);
            const twist=newAngle-pinchAngle;
            // Wrap angle delta to [-π, π]
            const twistDelta = twist - Math.round(twist/(Math.PI*2))*Math.PI*2;
            if(Math.abs(twistDelta)<0.3){ // ignore big jumps
              const lookAxis=new THREE.Vector3(0,0,1).applyQuaternion(camera.quaternion);
              G.quaternion.premultiply(
                new THREE.Quaternion().setFromAxisAngle(lookAxis, -twistDelta)
              );
            }
            pinchAngle=newAngle;
          }
          pinchD=d; pinchMid=mid;
        }
      },{passive:false});

      cvs.addEventListener("touchend",e=>{
        e.preventDefault();
        if(e.touches.length===0){ prev2=null; pinchD=null; pinchMid=null; pinchAngle=null; }
        if(e.touches.length===1){
          pinchD=null; pinchMid=null;
          prev2={x:e.touches[0].clientX,y:e.touches[0].clientY};
          velX=0; velY=0;
        }
      },{passive:false});

      // ── Mouse ──────────────────────────────────────────
      let mouseDown=false, mouseBtn=0, mousePrev=null;
      cvs.addEventListener("mousedown",e=>{
        mouseDown=true; mouseBtn=e.button;
        mousePrev={x:e.clientX,y:e.clientY};
        velX=0; velY=0;
      });
      cvs.addEventListener("mousemove",e=>{
        if(!mouseDown||!mousePrev)return;
        const dx=e.clientX-mousePrev.x, dy=e.clientY-mousePrev.y;
        rotateGlobe(dx,dy);
        velX=dx; velY=dy;
        mousePrev={x:e.clientX,y:e.clientY};
      });
      cvs.addEventListener("mouseup",()=>{mouseDown=false;});
      cvs.addEventListener("contextmenu",e=>e.preventDefault());
      cvs.addEventListener("wheel",e=>{
        e.preventDefault();
        camera.position.z=Math.max(150,Math.min(900,camera.position.z*(1+e.deltaY*0.0008)));
      },{passive:false});

      let frame=0;
      function animate(){
        animId=requestAnimationFrame(animate); animIdRef.current=animId;
        if(pausedRef.current){ renderer.render(scene,camera); return; } // freeze physics, keep rendering
        frame++;

        // Auto-rotation disabled — user controls rotation manually
        // Inertia: coast after finger lift, decay with friction
        if(Math.abs(velX)>0.01||Math.abs(velY)>0.01){
          rotateGlobe(velX,velY);
          velX*=FRICTION; velY*=FRICTION;
        }

        // ── Missiles ──────────────────────────────────────
        for(let i=missiles.length-1;i>=0;i--){
          const m=missiles[i];if(m.dead){missiles.splice(i,1);continue;}
          m.frameCount++;

          // ── Threat awareness ───────────────────────────────
          // Missile checks if it's inside any bear's radar range.
          // Only starts evasive curves once it detects a threat.
          if(!m.threatRange){
            for(let bi2=0;bi2<BEARS.length;bi2++){
              if(siteHpRef[bi2]>0 && m.pos.distanceTo(BEARS[bi2].vec)<RADAR_RANGE){
                m.threatRange=true; break;
              }
            }
          }

          // ── Deviation curve logic ──────────────────────────
          // Only evade when inside threat range. Picks a random 3D axis
          // (not just yaw) — missile can arc up, down, left, right, diagonally.
          if(m.threatRange && !m.curving && m.evasionBudget > 0 && m.frameCount % CURVE_INTERVAL === 0 && Math.random() < CURVE_CHANCE){
            m.curving = true;
            m.curveFrames = 0;
            // Pick a random axis in the tangent plane (any direction in 3D around vel)
            // This gives up/down/left/right/diagonal curves
            const normal = m.pos.clone().normalize();
            // Random vector, projected onto tangent plane = random tangent direction
            const randVec = new THREE.Vector3(Math.random()-0.5, Math.random()-0.5, Math.random()-0.5).normalize();
            let tangentAxis = randVec.sub(normal.clone().multiplyScalar(normal.dot(randVec)));
            if(tangentAxis.length() < 0.001) tangentAxis.set(0,1,0);
            m.curveAxis = tangentAxis.normalize();
            m.mesh.children.forEach(c=>{if(c.material)c.material.color.setHex(0xff8800);});
          }

          if(m.curving){
            m.curveFrames++;
            // Rotate vel around the chosen 3D tangent axis — creates curves in any plane
            m.vel.applyAxisAngle(m.curveAxis, CURVE_RATE);
            m.vel.normalize();
            if(m.curveFrames >= CURVE_FRAMES){
              m.curving = false;
              m.evasionBudget--; // spend one maneuver from budget
              m.mesh.children.forEach(c=>{if(c.material)c.material.color.setHex(0xff2200);});
            }
          }

          // Weak homing when curving, full homing when flying straight
          const MISSILE_MAX_TURN = 0.042;
          const steerStrength = m.curving ? 0.006 : MISSILE_MAX_TURN;
          m.vel = steerVel(m.pos, m.vel, m.targetPos, steerStrength);

          // Smooth ballistic arc: altitude = sin(progress) * APEX
          // progress = how far along the great-circle from launch to target
          {
            const startAngle = m.startNorm.angleTo(m.targetNorm);
            const curAngle   = m.startNorm.angleTo(m.pos.clone().normalize());
            const progress   = startAngle > 0.001 ? Math.min(1, curAngle / startAngle) : 1;
            const APEX       = 72;
            const arcAlt     = Math.max(1.5, APEX * Math.sin(progress * Math.PI));
            var moved = moveOnSphere(m.pos, m.vel, MISSILE_SPEED, arcAlt);
          }
          m.pos=moved.pos; m.vel=moved.vel;
          m.mesh.position.copy(m.pos);
          // Orient missile along velocity direction
          const mUp = m.vel.clone().normalize();
          const mRight = new THREE.Vector3().crossVectors(mUp, m.pos.clone().normalize()).normalize();
          if(mRight.length()>0.001) m.mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), mUp);
          m.trail.add(m.pos);

          // Impact check AFTER move (catches overshoot cases too)
          const distToTarget=m.distToTarget();
          if(distToTarget<SITE_HIT_DIST){
            explode(m.pos.clone(),0xff2200,1.8);
            G.remove(m.mesh);m.trail.dispose();m.dead=true;
            const bi=m.targetBearIdx;
            if(siteHpRef[bi]>0){
              siteHpRef[bi]--;updateSiteVisual(bi);
              if(siteHpRef[bi]===0){
                explode(BEARS[bi].vec.clone().normalize().multiplyScalar(GLOBE_R+FLY_ALT),0xff4400,2.5);
                showEv(`💥 BASE ${bi+1} DESTROYED`,"#f87171","Air defence offline");
                // Check if ALL bases are destroyed
                if(!gameOverFired.current && siteHpRef.every(hp=>hp<=0)){
                  gameOverFired.current = true;
                  clearTimeout(waveTimeout);
                  cancelAnimationFrame(animId);
                  setTimeout(()=>{
                    const report = {
                      launched, impacts, iceptLaunched, intercepted,
                      waves: waveNum,
                      timestamp: Date.now()
                    };
                    setGameOver(report);
                    onGameOver(report);
                  }, 2000);
                }
              }
              else showEv(`💥 HIT! BASE ${bi+1}`,"#fb923c",`HP: ${siteHpRef[bi]}/${MAX_HP}`);
            }
            impacts++;setStats(s=>({...s,h:impacts}));missiles.splice(i,1);
          } else if(m.frameCount>3600){
            // Very old missile — detonate it where it is, count as miss (no HP damage)
            explode(m.pos.clone(),0xff6600,0.9);
            G.remove(m.mesh);m.trail.dispose();m.dead=true;missiles.splice(i,1);
          }
        }

        if(frame%5===0) checkRadar();

        // ── Interceptors ──────────────────────────────────
        for(let i=icepts.length-1;i>=0;i--){
          const iv=icepts[i];
          // If target is dead, try to reroute to the nearest active missile
          if(iv.dead){ G.remove(iv.mesh); iv.trail.dispose(); icepts.splice(i,1); continue; }
          iv.age++;
          // Lifetime expired — fuel out, gravity pulls it back down gradually
          if(iv.age > ICEPT_MAX_AGE){
            // Accumulate gravity velocity — starts slow, accelerates naturally
            if(!iv.gravVel) iv.gravVel = 0;
            iv.gravVel += 0.012; // slow acceleration
            iv.gravVel = Math.min(iv.gravVel, 0.38); // terminal ~2x flight speed
            const inward = iv.pos.clone().normalize().multiplyScalar(-iv.gravVel);
            iv.pos.add(inward);
            iv.mesh.position.copy(iv.pos);
            iv.trail.add(iv.pos);
            if(iv.pos.length() <= GLOBE_R + 2){
              explode(iv.pos.clone(), 0x00aaff, 1.2);
              G.remove(iv.mesh); iv.trail.dispose(); iv.dead=true; icepts.splice(i,1);
            }
            continue;
          }
          if(iv.target.dead){
            // Find nearest alive missile
            let nearest=null, nearDist=Infinity;
            missiles.forEach(m2=>{ if(!m2.dead){ const d=iv.pos.distanceTo(m2.pos); if(d<nearDist){nearDist=d;nearest=m2;} } });
            if(nearest){
              // Reroute: update target and reset track
              iv.target = nearest;
              iv.track = { pos: nearest.pos.clone(), vel: nearest.vel.clone() };
              iv.trackAge = 0;
              // Don't destroy — keep flying
            } else {
              // No missiles left — interceptor self-destructs gracefully
              explode(iv.pos.clone(), 0x00aaff, 0.6);
              G.remove(iv.mesh); iv.trail.dispose(); iv.dead=true; icepts.splice(i,1); continue;
            }
          }
          // Recompute intercept every frame (adapts to evasion)
          // Radar track update: refresh every 45 frames (radar sweep rate)
          // Only if missile is within radar detection range of the launching bear
          iv.trackAge++;
          // Radar update every 90 frames — slower, noisier, truly stale
          iv.track.age = (iv.track.age||0) + 1;
          if(iv.trackAge%90===0){
            const bearIdx = BEARS.findIndex(b=>b.vec && iv.target.pos.distanceTo(b.vec)<RADAR_RANGE);
            if(bearIdx>=0 && siteHpRef[bearIdx]>0){
              const noiseDir = new THREE.Vector3(Math.random()-0.5,Math.random()-0.5,Math.random()-0.5).normalize();
              iv.track.pos = iv.target.pos.clone().addScaledVector(noiseDir, 5+Math.random()*5);
              iv.track.vel = iv.target.vel.clone()
                .add(new THREE.Vector3((Math.random()-0.5)*0.15,(Math.random()-0.5)*0.15,(Math.random()-0.5)*0.15))
                .normalize();
              iv.track.age = 0; // reset staleness on fresh update
            }
          }
          const aim=computeIntercept(iv.pos,iv.vel,iv.track);
          // Interceptor climbs from ground, tracks missile altitude
          // True 3D steering — no altitude argument, no speed burst
          const moved=steerInterceptor(iv.pos,iv.vel,aim,ICEPT_SPEED);
          if(!isNaN(moved.pos.x)){ iv.pos=moved.pos; iv.vel=moved.vel; }
          iv.mesh.position.copy(iv.pos);iv.trail.add(iv.pos);
          if(iv.pos.distanceTo(iv.target.pos)<HIT_DIST){
            explode(iv.pos.clone(),0x00ddff,1.1);
            iv.target.dead=true;G.remove(iv.target.mesh);iv.target.trail.dispose();
            G.remove(iv.mesh);iv.trail.dispose();iv.dead=true;
            intercepted++;interceptSinceRepair++;
            setStats(s=>({...s,i:intercepted}));
            const toRepair=REPAIR_EVERY-interceptSinceRepair;
            showEv("🛡️ INTERCEPTED!","#22d3ee",toRepair>0?`${toRepair} more for repair`:"Repair incoming...");
            if(interceptSinceRepair>=REPAIR_EVERY){interceptSinceRepair=0;setTimeout(tryRepair,1500);}
            icepts.splice(i,1);
          }
        }

        // Explosions
        for(let i=exps.length-1;i>=0;i--){const e=exps[i];e.age++;const p=e.age/e.max;e.fl.material.opacity=Math.max(0,0.9-p*5);e.fl.scale.setScalar(1+p*3);e.parts.forEach(({m,vel})=>{m.position.addScaledVector(vel,1);vel.multiplyScalar(0.91);m.material.opacity=Math.max(0,1-p*1.6);m.scale.setScalar(Math.max(0.01,(1-p*0.8)*e.sz));});if(e.age>=e.max){G.remove(e.grp);exps.splice(i,1);}}

        for(let i=beams.length-1;i>=0;i--){const b=beams[i];b.age++;b.mat.opacity=Math.max(0,1-b.age/b.max);if(b.age>=b.max){G.remove(b.line);beams.splice(i,1);}}

        if(frame%2===0){
          const t=Date.now()*0.003;
          bearBases.forEach((b,bi)=>{if(siteHpRef[bi]<=0)return;const s=0.85+0.15*Math.sin(t+b.phase);b.glow.scale.setScalar(s);b.halo.scale.setScalar(0.7+0.3*Math.sin(t+b.phase+1));b.halo.material.opacity=0.1+0.1*Math.sin(t+b.phase);});
          // Sonar-ping pulse — Gemini style: scale 0→1, fade 0.35→0
          bearRadars.forEach((r,bi)=>{
            r.pulseRings.forEach(pr=>{
              if(siteHpRef[bi]<=0){pr.mesh.material.opacity=0;return;}
              pr.age+=1.5; const t=pr.age%100;
              const s=0.01+(t/100); // scale from near-zero to 1 (full RADAR_RANGE)
              pr.mesh.scale.set(s,s,1);
              pr.mesh.material.opacity=(1-t/100)*0.35;
            });
          });
          penguinRadars.forEach(r=>r.update());
        }

        if(frame%10===0)setStats(s=>({...s,a:missiles.length}));
        renderer.render(scene,camera);
      }
      animate();
    }
    return()=>{script.remove();cancelAnimationFrame(animId);if(renderer)renderer.dispose();};
  },[]);

  const hpColor=hp=>hp===3?"#4ade80":hp===2?"#facc15":hp===1?"#f87171":"#333";

  return(
    <div style={{width:"100vw",height:"100dvh",background:"#000",position:"relative",overflow:"hidden",fontFamily:"'Courier New',monospace"}}>
      <div ref={mountRef} style={{width:"100%",height:"100%"}}/>
      <div style={{position:"absolute",top:0,left:0,right:0,padding:"10px 14px",background:"linear-gradient(to bottom,rgba(0,0,0,0.92) 70%,transparent)",pointerEvents:"none"}}>
        <div style={{color:"#e8e4dc",fontSize:12,marginBottom:6,fontStyle:"italic"}}>❄️ Cold War</div>
        <div style={{display:"flex",gap:14,fontSize:11,color:"#666",marginBottom:6}}>
          <span>LAUNCHED <b style={{color:"#4ade80"}}>{stats.l}</b></span>
          <span>INTERCEPTED <b style={{color:"#22d3ee"}}>{stats.i}</b></span>
          <span>IMPACTS <b style={{color:"#f87171"}}>{stats.h}</b></span>
          <span>ACTIVE <b style={{color:"#facc15"}}>{stats.a}</b></span>
          <span>WAVE <b style={{color:"#c084fc"}}>{stats.w}</b></span>
        </div>
        <div style={{display:"flex",gap:8,alignItems:"center"}}>
          {siteHp.map((hp,i)=>(
            <div key={i} style={{display:"flex",flexDirection:"column",alignItems:"center",gap:2}}>
              <div style={{fontSize:9,color:"#555"}}>B{i+1}</div>
              <div style={{display:"flex",gap:2}}>
                {[0,1,2].map(k=><div key={k} style={{width:6,height:6,borderRadius:"50%",background:k<hp?hpColor(hp):"#1a1a1a",boxShadow:k<hp?`0 0 4px ${hpColor(hp)}`:"none"}}/>)}
              </div>
            </div>
          ))}
          <div style={{fontSize:10,color:"#444",marginLeft:4,fontStyle:"italic"}}>Base HP</div>
        </div>
      </div>
      {evMsg&&(
        <div style={{position:"absolute",top:"45%",left:"50%",transform:"translate(-50%,-50%)",textAlign:"center",pointerEvents:"none"}}>
          <div style={{color:evMsg.col,fontSize:15,fontWeight:"bold"}}>{evMsg.txt}</div>
          {evMsg.sub&&<div style={{color:"#888",fontSize:11,marginTop:4,fontStyle:"italic"}}>{evMsg.sub}</div>}
        </div>
      )}
      {/* Control buttons — bottom bar */}
      {!gameOver && (
        <div style={{position:"absolute",bottom:16,left:0,right:0,display:"flex",justifyContent:"center",gap:12,zIndex:10,pointerEvents:"auto"}}>
          {/* Pause/Resume */}
          <button
            onClick={()=>{ const p=!pausedRef.current; pausedRef.current=p; setPaused(p); }}
            style={{padding:"7px 18px",background:"rgba(0,0,0,0.7)",border:"1px solid #333",
              color:paused?"#e8e4dc":"#666",fontFamily:"Georgia,serif",fontSize:12,cursor:"pointer",borderRadius:2}}
          >{paused ? "▶  Resume" : "⏸  Pause"}</button>

          {/* Exit — shows inline confirmation */}
          {!confirmExit
            ? <button
                onClick={()=>setConfirmExit(true)}
                style={{padding:"7px 18px",background:"rgba(0,0,0,0.7)",border:"1px solid #333",
                  color:"#666",fontFamily:"Georgia,serif",fontSize:12,cursor:"pointer",borderRadius:2}}
              >✕  Exit</button>
            : <>
                <span style={{color:"#888",fontFamily:"Georgia,serif",fontSize:12,lineHeight:"32px",padding:"0 4px"}}>Exit?</span>
                <button
                  onClick={()=>{ clearTimeout(waveTimerRef.current); cancelAnimationFrame(animIdRef.current); onExit(); }}
                  style={{padding:"7px 14px",background:"rgba(0,0,0,0.7)",border:"1px solid #aa6a6a",
                    color:"#aa6a6a",fontFamily:"Georgia,serif",fontSize:12,cursor:"pointer",borderRadius:2}}
                >Yes</button>
                <button
                  onClick={()=>setConfirmExit(false)}
                  style={{padding:"7px 14px",background:"rgba(0,0,0,0.7)",border:"1px solid #333",
                    color:"#666",fontFamily:"Georgia,serif",fontSize:12,cursor:"pointer",borderRadius:2}}
                >No</button>
              </>
          }
        </div>
      )}
      <div style={{position:"absolute",bottom:52,left:0,right:0,textAlign:"center",fontSize:10,color:"#1a1a1a",fontFamily:"Georgia,serif",fontStyle:"italic",pointerEvents:"none"}}>1-finger rotate  ·  2-finger pan  ·  pinch zoom  ·  twist</div>

      {gameOver && (
        <div style={{position:"absolute",inset:0,background:"rgba(0,0,0,0.92)",display:"flex",alignItems:"center",justifyContent:"center",zIndex:50,padding:"16px"}}>
          <div style={{fontFamily:"Georgia,'Times New Roman',serif",textAlign:"center",width:"100%",maxWidth:360}}>

            {/* Title */}
            <div style={{fontSize:32,marginBottom:8}}>{gameOver.bearsWin ? "🐻‍❄️" : "💥"}</div>
            <div style={{fontSize:22,color:gameOver.bearsWin?"#6aaa7a":"#aa6a6a",marginBottom:4,fontWeight:"bold"}}>
              {gameOver.bearsWin ? "Bears Win" : "Defeat"}
            </div>
            <div style={{fontSize:12,color:"#666",marginBottom:24,fontStyle:"italic"}}>
              {gameOver.bearsWin ? "All 10 waves survived" : "All bear bases destroyed"} — Wave {gameOver.waves}
            </div>

            {/* Penguin stats */}
            <div style={{background:"#0d0d0d",border:"1px solid #2a2a2a",borderRadius:2,padding:"14px 16px",marginBottom:10,textAlign:"left"}}>
              <div style={{fontSize:12,color:"#aa6a6a",marginBottom:10,fontStyle:"italic"}}>🐧 Penguin Missiles</div>
              <div style={{display:"flex",justifyContent:"space-between",marginBottom:6}}>
                <span style={{color:"#888",fontSize:13}}>Launched</span>
                <span style={{color:"#e8e4dc",fontSize:15,fontWeight:"bold"}}>{gameOver.launched}</span>
              </div>
              <div style={{display:"flex",justifyContent:"space-between",marginBottom:10}}>
                <span style={{color:"#888",fontSize:13}}>Hit targets</span>
                <span style={{color:"#aa6a6a",fontSize:15,fontWeight:"bold"}}>{gameOver.impacts}</span>
              </div>
              <div style={{background:"#111",borderRadius:3,height:6,overflow:"hidden"}}>
                <div style={{height:"100%",background:"#f87171",width:`${gameOver.launched>0?Math.round(gameOver.impacts/gameOver.launched*100):0}%`,transition:"width 1s"}}/>
              </div>
              <div style={{textAlign:"right",fontSize:13,color:"#f87171",fontWeight:"bold",marginTop:4}}>
                {gameOver.launched>0?Math.round(gameOver.impacts/gameOver.launched*100):0}% hit rate
              </div>
            </div>

            {/* Bear stats */}
            <div style={{background:"#0d0d0d",border:"1px solid #2a2a2a",borderRadius:2,padding:"14px 16px",marginBottom:20,textAlign:"left"}}>
              <div style={{fontSize:12,color:"#6aaa7a",marginBottom:10,fontStyle:"italic"}}>🐻‍❄️ Bear Interceptors</div>
              <div style={{display:"flex",justifyContent:"space-between",marginBottom:6}}>
                <span style={{color:"#888",fontSize:13}}>Launched</span>
                <span style={{color:"#e8e4dc",fontSize:15,fontWeight:"bold"}}>{gameOver.iceptLaunched}</span>
              </div>
              <div style={{display:"flex",justifyContent:"space-between",marginBottom:10}}>
                <span style={{color:"#888",fontSize:13}}>Successful intercepts</span>
                <span style={{color:"#6aaa7a",fontSize:15,fontWeight:"bold"}}>{gameOver.intercepted}</span>
              </div>
              <div style={{background:"#111",borderRadius:3,height:6,overflow:"hidden"}}>
                <div style={{height:"100%",background:"#22d3ee",width:`${gameOver.iceptLaunched>0?Math.round(gameOver.intercepted/gameOver.iceptLaunched*100):0}%`,transition:"width 1s"}}/>
              </div>
              <div style={{textAlign:"right",fontSize:13,color:"#22d3ee",fontWeight:"bold",marginTop:4}}>
                {gameOver.iceptLaunched>0?Math.round(gameOver.intercepted/gameOver.iceptLaunched*100):0}% success rate
              </div>
            </div>

            <button
              onClick={()=>setGameOver(null)}
              style={{width:"100%",padding:"13px",background:"transparent",border:"1px solid #2a2a2a",
                color:"#888",fontFamily:"Georgia,'Times New Roman',serif",fontSize:13,cursor:"pointer"}}
              onMouseEnter={e=>e.target.style.borderColor="#e8e4dc"}
              onMouseLeave={e=>e.target.style.borderColor="#2a2a2a"}
            >📋  View History</button>
          </div>
        </div>
      )}
    </div>
  );
}

// ── Shell: manages start screen, restart, and battle history ──
export default function Shell() {
  const [runId, setRunId]     = useState(0);
  const [history, setHistory] = useState([]);
  const [view, setView]       = useState("start"); // "start" | "sim" | "history"

  useEffect(()=>{
    (async()=>{
      try{
        const r = await window.storage.get("battle-history");
        if(r) setHistory(JSON.parse(r.value));
      }catch(_){}
    })();
  },[]);

  function handleGameOver(report){
    setHistory(prev=>{
      const next = [report, ...prev].slice(0, 50);
      window.storage.set("battle-history", JSON.stringify(next)).catch(()=>{});
      return next;
    });
    setView("history");
  }

  function startBattle(){
    setView("sim");
    setRunId(id => id + 1);
  }

  const fmt = ts => {
    const d = new Date(ts);
    return d.toLocaleDateString()+' '+d.toLocaleTimeString([], {hour:'2-digit',minute:'2-digit'});
  };

  const btn = (onClick, color, children) => (
    <button onClick={onClick} style={{
      width:"100%", padding:"14px 0", background:"transparent",
      border:`1px solid ${color}22`, color, cursor:"pointer",
      fontFamily:"Georgia,'Times New Roman',serif", fontSize:14,
      marginBottom:12, letterSpacing:0
    }}
    onMouseEnter={e=>{e.target.style.background=`${color}12`;e.target.style.borderColor=color;}}
    onMouseLeave={e=>{e.target.style.background="transparent";e.target.style.borderColor=`${color}22`;}}
    >{children}</button>
  );

  return (
    <div style={{width:"100vw",height:"100dvh",background:"#000",position:"relative",fontFamily:"Georgia,'Times New Roman',serif"}}>

      {/* Start screen */}
      {view==="start" && (
        <div style={{position:"absolute",inset:0,display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"space-between",padding:"28px 24px 20px"}}>

          {/* Title */}
          <div style={{textAlign:"center"}}>
            <div style={{fontSize:14,color:"#aaa",marginBottom:10,fontStyle:"italic"}}>Strategic Simulation</div>
            <div style={{fontSize:42,color:"#fff",fontWeight:"bold",letterSpacing:2}}>❄️ Cold War ❄️</div>
            <div style={{width:50,height:1,background:"#444",margin:"12px auto"}}/>
            <div style={{fontSize:14,color:"#ccc",fontStyle:"italic"}}>Penguin ICBMs vs Arctic Bear Air Defence</div>
          </div>

          {/* Buttons */}
          <div style={{maxWidth:320,width:"100%"}}>
            {btn(startBattle, "#fff", "▶  Start Simulation")}
            {btn(()=>setView("history"), "#fff", "📋  Battle History")}
          </div>

          {/* Attribution */}
          <div style={{color:"#888",fontSize:13,fontStyle:"italic",textAlign:"center"}}>
            Made with ❤️ by Claude
          </div>

        </div>
      )}

      {/* Simulation — only mounted when view is sim */}
      {view==="sim" && <App key={runId} onGameOver={handleGameOver} onExit={()=>setView("start")} />}

      {/* History overlay */}
      {view==="history" && (
        <div style={{position:"absolute",inset:0,background:"rgba(0,0,0,0.93)",zIndex:100,overflow:"auto",padding:"24px 16px"}}>
          <div style={{maxWidth:380,margin:"0 auto"}}>
            <div style={{color:"#e8e4dc",fontSize:18,marginBottom:6,fontWeight:"bold"}}>📋 Battle History</div>
            <div style={{color:"#555",fontSize:12,marginBottom:20,fontStyle:"italic"}}>{history.length} battles recorded</div>

            {history.map((r,idx)=>(
              <div key={r.timestamp} style={{
                border:"1px solid #1a2a1a",marginBottom:10,padding:"10px 12px",
                background:idx===0?"rgba(0,255,100,0.03)":"transparent"
              }}>
                <div style={{display:"flex",justifyContent:"space-between",marginBottom:8}}>
                  <span style={{color:r.bearsWin?"#6aaa7a":"#aa6a6a",fontSize:12}}>
                    {idx===0?"● ":""}{r.bearsWin?"🐻‍❄️ Bears Win":"💥 Penguins Win"} — Wave {r.waves}
                  </span>
                  <span style={{color:"#555",fontSize:11,fontStyle:"italic"}}>{fmt(r.timestamp)}</span>
                </div>
                <table style={{width:"100%",fontSize:10,borderCollapse:"collapse"}}>
                  <tbody>
                    <tr>
                      <td style={{color:"#555",padding:"2px 0"}}>Missiles</td>
                      <td style={{color:"#f87171",textAlign:"right"}}>{r.impacts}/{r.launched}</td>
                      <td style={{color:r.impacts/r.launched>0.5?"#f87171":"#facc15",textAlign:"right",paddingLeft:8}}>
                        {r.launched>0?Math.round(r.impacts/r.launched*100):0}%
                      </td>
                    </tr>
                    <tr>
                      <td style={{color:"#555",padding:"2px 0"}}>Interceptors</td>
                      <td style={{color:"#22d3ee",textAlign:"right"}}>{r.intercepted}/{r.iceptLaunched}</td>
                      <td style={{color:r.intercepted/r.iceptLaunched>0.5?"#4ade80":"#facc15",textAlign:"right",paddingLeft:8}}>
                        {r.iceptLaunched>0?Math.round(r.intercepted/r.iceptLaunched*100):0}%
                      </td>
                    </tr>
                  </tbody>
                </table>
              </div>
            ))}

            {history.length===0 && (
              <div style={{color:"#333",fontSize:13,textAlign:"center",marginTop:40,fontStyle:"italic"}}>No battles yet</div>
            )}

            <button
              onClick={()=>setView("start")}
              style={{width:"100%",marginTop:16,padding:"12px",background:"transparent",
                border:"1px solid #2a2a2a",color:"#888",
                fontFamily:"Georgia,'Times New Roman',serif",fontSize:13,cursor:"pointer"}}
              onMouseEnter={e=>e.target.style.borderColor="#e8e4dc"}
              onMouseLeave={e=>e.target.style.borderColor="#2a2a2a"}
            >▶  Back to Start</button>
          </div>
        </div>
      )}
    </div>
  );
}
