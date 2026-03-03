import { useEffect, useRef, useState } from "react";

const GLOBE_R       = 130;
const FLY_ALT       = 52;     // single altitude — missiles AND interceptors fly here
const MISSILE_SPEED = 0.162;  // reduced 10% — jets now share the skies
const ICEPT_SPEED   = 0.1854; // 0.18 * 1.03
const JET_SPEED     = 0.1854; // same as interceptors
const JET_ALT       = 38;     // slightly below missile altitude
const JET_LAUNCH_RANGE = 50;  // units from bear base before jets drop their missiles
const JET_MISSILE_SPEED = 0.1854; // same speed as jets
const JET_MISSILE_MAX_AGE = 260; // short range — about 57 units max travel
const JET_WAVES     = new Set([5,6,8,9,10]);
const RADAR_RANGE   = 115;
// Wave system defined in init
const DETECT_DELAY  = 700;
const HIT_DIST      = 1.5;    // kinetic hit-to-kill — very tight
const SITE_HIT_DIST = 2.0;    // direct hit on structure required
const MAX_HP        = 3;
const REPAIR_EVERY  = 3;
// Evasion
const CURVE_INTERVAL = 100;   // frames between starting a new deviation curve
const CURVE_CHANCE   = 0.40;  // probability of beginning a curve
const CURVE_RATE     = 0.018; // radians per frame — constant turn applied every frame
const EVASION_BUDGET  = 1;     // max number of evasion maneuvers per missile lifetime
const CURVE_FRAMES   = 110;
const ICEPT_MAX_AGE  = 550; // frames before interceptor runs out of fuel (~9s)
const MAX_ICEPT_PER_MISSILE = 2; // max interceptors globally targeting same missile   // how many frames the curve lasts

function App({ onGameOver, onExit }) {
  const mountRef = useRef(null);
  const [stats, setStats]   = useState({ l:0, i:0, h:0, a:0, w:0, il:0 });
  const [gameOver, setGameOver] = useState(null);
  const [siteHp, setSiteHp] = useState([3,3,3,3,3]);
  const [paused, setPaused] = useState(false);
  const [speed, setSpeed] = useState(1);
  const [confirmExit, setConfirmExit] = useState(false);
  const [fps, setFps] = useState(60);
  const fpsLogRef = useRef([]);
  const pausedRef     = useRef(false);
  const animIdRef     = useRef(null);
  const waveTimerRef  = useRef(null);
  const gameOverFired = useRef(false);
  const speedRef = useRef(1);

  useEffect(() => {
    let THREE;
    let scene, camera, renderer, G;
    let launched=0, intercepted=0, impacts=0, interceptSinceRepair=0, iceptLaunched=0;
    const missiles=[], icepts=[], exps=[], beams=[], jets=[], jetMissiles=[];
    const bearBases=[], bearRadars=[], penguinRadars=[];
    const detectionLog = new Set();
    let midCounter = 0;
    const siteHpRef = [3,3,3,3,3];

    // ── US Airbases (southern USA) ─────────────────────────────────────────
    // 3 bases: west coast (Nellis NV), central (Dyess TX), east coast (Shaw SC)
    const US_AIRBASES = [
      {lat:36.2, lng:-115.0}, // Nellis AFB, Nevada
      {lat:32.4, lng:-99.8},  // Dyess AFB, Texas
      {lat:33.9, lng:-80.5},  // Shaw AFB, South Carolina
    ].map(b=>({...b, vec:null}));


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
      const staleness = Math.min(1, track.age / 30);

      // Lead time estimate — how many frames until we reach the missile
      const leadFrames = Math.min(dist / ICEPT_SPEED, 70);

      // Project missile forward along its observed velocity
      // Staleness reduces lead — when data is old, aim closer to last known position
      const lead = leadFrames * (1 - staleness * 0.7);
      const aimed = track.pos.clone()
        .addScaledVector(track.vel, lead * MISSILE_SPEED);

      // Arc-aware altitude: extrapolate altitude trend observed across radar updates
      // track.altVel = altitude change per frame, computed on each radar refresh
      const currentAlt = track.pos.length() - GLOBE_R;
      const altVel = track.altVel || 0;
      const estimatedAlt = Math.max(1, currentAlt + altVel * lead);
      aimed.normalize().multiplyScalar(GLOBE_R + estimatedAlt);
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

      // ── Flags ──────────────────────────────────────────────
      const flags=[]; // {flagMesh, flagGeo, normal} for wave animation
      function mkFlag(emoji, surfaceVec, flagColor){
        const up = surfaceVec.clone().normalize(); // radially outward = "up" for the flag

        // Stable tangent frame — robust at any latitude including poles
        const worldY = new THREE.Vector3(0,1,0);
        let east = new THREE.Vector3().crossVectors(worldY, up);
        if(east.length() < 0.01){
          // Near pole — use world X instead
          east = new THREE.Vector3().crossVectors(new THREE.Vector3(1,0,0), up);
        }
        east.normalize();
        const north = new THREE.Vector3().crossVectors(up, east).normalize();

        const basePos = up.clone().multiplyScalar(GLOBE_R + 0.3);
        const POLE_H = 10;

        // Thick pole — half buried, so it roots into the ground visually
        const poleMat = new THREE.MeshPhongMaterial({color:0x888888, shininess:60});
        const pole = new THREE.Mesh(new THREE.CylinderGeometry(0.28,0.35,POLE_H+2,8), poleMat);
        pole.position.copy(basePos.clone().addScaledVector(up, POLE_H*0.5 - 1));
        pole.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), up);
        G.add(pole);

        // Flag canvas — big emoji, clean colored background
        const fc = document.createElement("canvas"); fc.width=128; fc.height=80;
        const fctx = fc.getContext("2d");
        // Background with slight gradient feel
        fctx.fillStyle = flagColor;
        fctx.fillRect(0,0,128,80);
        // Thin border
        fctx.strokeStyle = "rgba(255,255,255,0.25)";
        fctx.lineWidth = 2;
        fctx.strokeRect(1,1,126,78);
        // Emoji centered
        fctx.font = "52px serif";
        fctx.textAlign = "center"; fctx.textBaseline = "middle";
        fctx.fillText(emoji, 64, 42);
        const tex = new THREE.CanvasTexture(fc);

        // Flag mesh — 6 segments wide, 2 tall for smooth travelling wave
        const FW=6, FH=4;
        const flagGeo = new THREE.PlaneGeometry(FW,FH,8,2);
        const flagMat = new THREE.MeshBasicMaterial({map:tex, side:THREE.DoubleSide, transparent:true, opacity:0.95});
        const flagMesh = new THREE.Mesh(flagGeo, flagMat);

        // Build rotation matrix from stable local frame
        // Flag faces "north", hangs along "east", up is surface normal
        const m4 = new THREE.Matrix4();
        m4.makeBasis(east, up, north);
        flagMesh.quaternion.setFromRotationMatrix(m4);

        // Position: top of pole, offset half flag-width along east so left edge touches pole
        const poleTop = basePos.clone().addScaledVector(up, POLE_H + 0.5);
        // Offset down FH/2 so top edge of flag sits at pole top, not center
        flagMesh.position.copy(poleTop.clone().addScaledVector(east, FW*0.5).addScaledVector(up, -FH*0.5));

        G.add(flagMesh);

        // Store original Y positions for wave deformation
        const posAttr = flagGeo.attributes.position;
        const restY = new Float32Array(posAttr.count);
        for(let k=0;k<posAttr.count;k++) restY[k] = posAttr.getY(k);

        flags.push({
          flagMesh, flagGeo, posAttr, restY,
          phase: Math.random()*Math.PI*2,
          FW, FH
        });
        return flagMesh;
      }

      PENGUINS.forEach(s=>{s.vec=ll2v(s.lat,s.lng);});
      {
        const c=new THREE.Vector3();
        PENGUINS.forEach(s=>c.add(s.vec));
        c.normalize().multiplyScalar(GLOBE_R);
        mkFlag("🐧", c, "#1a3a5c");
      }

      BEARS.forEach((s,bi)=>{
        s.vec=ll2v(s.lat,s.lng);
        const n=s.vec.clone().normalize();
        // ── SAM Site ─────────────────────────────────────────
        let tUp=new THREE.Vector3(0,1,0);if(Math.abs(n.dot(tUp))>0.9)tUp.set(1,0,0);
        const r2=new THREE.Vector3().crossVectors(n,tUp).normalize();
        const u2=new THREE.Vector3().crossVectors(r2,n).normalize();
        const baseCol=0x00ff88;
        const padMat=new THREE.MeshPhongMaterial({color:0x334433,shininess:10});
        const glowMat=new THREE.MeshPhongMaterial({color:baseCol,emissive:baseCol,emissiveIntensity:0.4,shininess:40});

        // Concrete pad
        const pad=new THREE.Mesh(new THREE.CylinderGeometry(2.2,2.4,0.25,10),padMat);
        pad.position.copy(n.clone().multiplyScalar(GLOBE_R+0.15));
        pad.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),n);
        G.add(pad);

        // Radar dish — disc on short arm
        const dishArm=new THREE.Mesh(new THREE.CylinderGeometry(0.12,0.12,1.1,5),glowMat);
        dishArm.position.copy(n.clone().multiplyScalar(GLOBE_R+0.9));
        dishArm.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),n);
        G.add(dishArm);
        const dish=new THREE.Mesh(new THREE.CylinderGeometry(1.0,0.1,0.18,12),glowMat);
        dish.position.copy(n.clone().multiplyScalar(GLOBE_R+1.6));
        dish.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),n);
        G.add(dish);

        // Two launch canisters angled outward
        const canMat=new THREE.MeshPhongMaterial({color:baseCol,emissive:baseCol,emissiveIntensity:0.3,shininess:50});
        const canisterMeshes=[];
        [-1,1].forEach(side=>{
          const off=r2.clone().multiplyScalar(side*1.1);
          const canBase=n.clone().multiplyScalar(GLOBE_R+0.4).add(off);
          // Tilt canister ~40° outward from surface normal
          const tiltAxis=u2.clone();
          const canDir=n.clone().applyAxisAngle(tiltAxis, side*0.65).normalize();
          const can=new THREE.Mesh(new THREE.CylinderGeometry(0.22,0.22,1.6,6),canMat);
          can.position.copy(canBase.clone().addScaledVector(canDir,0.8));
          can.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),canDir);
          G.add(can);
          canisterMeshes.push(can);
        });

        // HP dots — tiny, close to pad
        const hpDots=[];
        for(let k=0;k<MAX_HP;k++){
          const ang=k/MAX_HP*Math.PI*2;
          const dot=new THREE.Mesh(new THREE.SphereGeometry(0.4,5,5),new THREE.MeshBasicMaterial({color:baseCol,transparent:true,opacity:1}));
          dot.position.copy(n.clone().multiplyScalar(GLOBE_R+0.6).add(r2.clone().multiplyScalar(Math.cos(ang)*2.8)).add(u2.clone().multiplyScalar(Math.sin(ang)*2.8)));
          G.add(dot);hpDots.push(dot);
        }

        // glow/halo — kept as invisible refs for updateSiteVisual compat
        const glow=dish; const halo=dishArm;
        // Store colorable meshes for damage coloring
        const siteMeshes=[dish,dishArm,...canisterMeshes];
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
        bearBases.push({glow,halo,siteMeshes,phase:Math.random()*Math.PI*2,hpDots});
        bearRadars.push({pulseRings,normal:n,bi,pulseColor:0x00ff88});
      });
      {
        const c=new THREE.Vector3();
        BEARS.forEach(s=>c.add(s.vec));
        c.normalize().multiplyScalar(GLOBE_R);
        mkFlag("🐻‍❄️", c, "#1a0a00");
      }

      function mkRings(sv,color){
        const n=sv.clone().normalize(),bp=n.clone().multiplyScalar(GLOBE_R+1.2);
        let up=new THREE.Vector3(0,1,0);if(Math.abs(n.dot(up))>0.9)up.set(1,0,0);
        const r2=new THREE.Vector3().crossVectors(n,up).normalize();
        const u2=new THREE.Vector3().crossVectors(r2,n).normalize();
        const rings=[];
        for(let i=0;i<3;i++){const pts=[];for(let j=0;j<=48;j++){const a=j/48*Math.PI*2,r=14;const wp=new THREE.Vector3().addScaledVector(r2,Math.cos(a)*r).addScaledVector(u2,Math.sin(a)*r).add(bp);wp.normalize().multiplyScalar(GLOBE_R+1.5);pts.push(wp.clone());}const mat=new THREE.LineBasicMaterial({color,transparent:true,opacity:0});const line=new THREE.Line(new THREE.BufferGeometry().setFromPoints(pts),mat);G.add(line);rings.push({line,mat,t:i/3});}
        return{rings,update(){this.rings.forEach(r=>{r.t+=0.012;if(r.t>1)r.t-=1;const s=0.3+r.t*1.7;r.line.scale.set(s,s,s);r.mat.opacity=r.t<0.1?r.t/0.1*0.8:Math.max(0,(1-r.t)*0.8);});},flash(){this.rings.forEach(r=>{r.mat.opacity=1;r.t=0.05;});}};
      }
      PENGUINS.forEach(s=>{
        const pn=s.vec.clone().normalize();
        // Concrete launch pad
        const ppMat=new THREE.MeshPhongMaterial({color:0x555544,shininess:5});
        const pp=new THREE.Mesh(new THREE.CylinderGeometry(1.8,2.0,0.22,10),ppMat);
        pp.position.copy(pn.clone().multiplyScalar(GLOBE_R+0.12));
        pp.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),pn);
        G.add(pp);
        // Silo tube — pointing along surface normal
        const silMat=new THREE.MeshPhongMaterial({color:0x884422,emissive:0x441100,shininess:30});
        const silo=new THREE.Mesh(new THREE.CylinderGeometry(0.42,0.48,2.2,8),silMat);
        silo.position.copy(pn.clone().multiplyScalar(GLOBE_R+1.35));
        silo.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),pn);
        G.add(silo);
        // Silo opening ring
        const ringMat=new THREE.MeshBasicMaterial({color:0x221100});
        const ring=new THREE.Mesh(new THREE.TorusGeometry(0.42,0.09,6,12),ringMat);
        ring.position.copy(pn.clone().multiplyScalar(GLOBE_R+2.5));
        ring.quaternion.setFromUnitVectors(new THREE.Vector3(0,0,1),pn);
        G.add(ring);
        penguinRadars.push({update:()=>{},flash:()=>{}});
      });

      const TL=14;
      function mkTrail(color,op=0.9){
        const buf=new Float32Array(TL*3);
        const attr=new THREE.BufferAttribute(buf,3);
        const geo=new THREE.BufferGeometry();
        geo.setAttribute('position',attr);
        geo.setDrawRange(0,0);
        const mat=new THREE.LineBasicMaterial({color,transparent:true,opacity:op});
        const line=new THREE.Line(geo,mat);
        G.add(line);
        const pts=[];
        return{pts,line,geo,mat,
          add(v){
            pts.push(v.clone());
            if(pts.length>TL)pts.shift();
            if(pts.length>=2){
              for(let i=0;i<pts.length;i++){buf[i*3]=pts[i].x;buf[i*3+1]=pts[i].y;buf[i*3+2]=pts[i].z;}
              attr.needsUpdate=true;
              geo.setDrawRange(0,pts.length);
              mat.opacity=Math.min(op,pts.length/TL);
            }
          },
          dispose(){G.remove(line);geo.dispose();}
        };
      }

      const EG=new THREE.SphereGeometry(1,4,4);
      function explode(pos,color,sz=1){const grp=new THREE.Group();grp.position.copy(pos);const parts=[];for(let i=0;i<14;i++){const m=new THREE.Mesh(EG,new THREE.MeshBasicMaterial({color,transparent:true,opacity:1}));m.scale.setScalar(sz*0.8);const th=Math.random()*Math.PI*2,ph=Math.acos(2*Math.random()-1),spd=(0.5+Math.random()*1.3)*sz;const vel=new THREE.Vector3(Math.sin(ph)*Math.cos(th),Math.cos(ph),Math.sin(ph)*Math.sin(th)).multiplyScalar(spd);parts.push({m,vel});grp.add(m);}const fl=new THREE.Mesh(new THREE.SphereGeometry(5*sz,6,6),new THREE.MeshBasicMaterial({color:0xffffff,transparent:true,opacity:0.9}));grp.add(fl);G.add(grp);exps.push({grp,parts,fl,age:0,max:45,sz});}

      function spawnBeam(vec){const mat=new THREE.LineBasicMaterial({color:0x00ffcc,transparent:true,opacity:1});const line=new THREE.Line(new THREE.BufferGeometry().setFromPoints([vec.clone().normalize().multiplyScalar(GLOBE_R+2),vec.clone().normalize().multiplyScalar(GLOBE_R+32)]),mat);G.add(line);beams.push({line,mat,age:0,max:18});}

      function updateSiteVisual(bi){
        const hp=siteHpRef[bi];
        const colors=[0x00ff88,0x00ff88,0xffcc00,0xff4400];
        const col=hp>0?colors[MAX_HP-hp]:0x333333;
        const b=bearBases[bi];
        if(b.siteMeshes) b.siteMeshes.forEach(m=>{
          m.material.color.setHex(col);
          if(m.material.emissive) m.material.emissive.setHex(hp>0?col:0x111111);
        });
        bearRadars[bi].pulseColor=col;
        bearRadars[bi].pulseRings.forEach(r=>r.mesh.material.color.setHex(col));
        b.hpDots.forEach((d,k)=>{d.material.color.setHex(k<hp?col:0x222222);d.material.opacity=k<hp?1:0.2;});
        setSiteHp([...siteHpRef]);
      }

      function tryRepair(){
        let worst=-1,worstHp=MAX_HP;
        siteHpRef.forEach((hp,i)=>{if(hp>0&&hp<worstHp){worstHp=hp;worst=i;}});
        if(worst>=0){siteHpRef[worst]=Math.min(MAX_HP,siteHpRef[worst]+1);updateSiteVisual(worst);}
      }

      // ── F22 RAPTOR ────────────────────────────────────────
      function mkF22Mesh(){
        // Scale: 0.67x smaller than before
        const S = 0.67;
        const grp = new THREE.Group();
        const bodyMat  = new THREE.MeshPhongMaterial({color:0x5a6b7a, emissive:0x0d1a22, shininess:100});
        const darkMat  = new THREE.MeshPhongMaterial({color:0x3a4a58, emissive:0x080f14, shininess:40});
        const glowMat  = new THREE.MeshPhongMaterial({color:0xff6600, emissive:0xff3300, emissiveIntensity:1.2});
        const glassMat = new THREE.MeshPhongMaterial({color:0x99ccee, transparent:true, opacity:0.5, shininess:200});

        // Helper to scale a Float32Array of xyz triples
        function sv(arr){ return new Float32Array(arr.map(v=>v*S)); }

        // ── Fuselage: angular chined cross-section (stealth faceting) ──
        // Vertices: nose tip → 2 shoulder points → 4 mid → 4 tail
        const fv = sv([
           0,    0,    -4.2,   // 0 nose tip
          -0.3,  0.15, -2.2,   // 1 upper-left shoulder
           0.3,  0.15, -2.2,   // 2 upper-right shoulder
           0.3, -0.08, -2.2,   // 3 lower-right shoulder
          -0.3, -0.08, -2.2,   // 4 lower-left shoulder
          -0.6,  0.12, -0.2,   // 5 mid upper-left
           0.6,  0.12, -0.2,   // 6 mid upper-right
           0.6, -0.2,  -0.2,   // 7 mid lower-right
          -0.6, -0.2,  -0.2,   // 8 mid lower-left
          -0.58, 0.10,  2.2,   // 9 tail upper-left
           0.58, 0.10,  2.2,   // 10 tail upper-right
           0.58,-0.22,  2.2,   // 11 tail lower-right
          -0.58,-0.22,  2.2,   // 12 tail lower-left
        ]);
        const fuseGeo = new THREE.BufferGeometry();
        fuseGeo.setAttribute('position', new THREE.BufferAttribute(fv,3));
        fuseGeo.setIndex([
          // nose to shoulder
          0,2,1,  0,3,2,  0,4,3,  0,1,4,
          // shoulder to mid
          1,2,6,1,6,5,  2,3,7,2,7,6,  3,4,8,3,8,7,  4,1,5,4,5,8,
          // mid to tail
          5,6,10,5,10,9,  6,7,11,6,11,10,  7,8,12,7,12,11,  8,5,9,8,9,12,
          // tail cap
          9,10,11,9,11,12,
        ]);
        fuseGeo.computeVertexNormals();
        grp.add(new THREE.Mesh(fuseGeo, bodyMat));

        // ── Cranked-arrow delta wings — F22 signature ──
        // Inboard sweep ~42°, outboard kink at ~40% span, then shallower
        [-1,1].forEach(side=>{
          const geo = new THREE.BufferGeometry();
          const x = side;
          // 5 points per wing: root-LE, root-TE, kink-LE, kink-TE, tip-LE, tip-TE
          const v = sv([
            x*0.6,   0.0,  -1.6,   // 0 root leading edge
            x*0.6,   0.0,   1.8,   // 1 root trailing edge
            x*2.4,  -0.04,  0.2,   // 2 kink leading edge
            x*2.4,  -0.04,  1.8,   // 3 kink trailing edge
            x*3.8,  -0.07,  1.0,   // 4 tip leading edge
            x*3.6,  -0.07,  1.9,   // 5 tip trailing edge
          ]);
          geo.setAttribute('position', new THREE.BufferAttribute(v,3));
          if(side>0) geo.setIndex([0,2,1, 2,3,1, 2,4,3, 4,5,3]);
          else        geo.setIndex([0,1,2, 2,1,3, 2,3,4, 4,3,5]);
          geo.computeVertexNormals();
          grp.add(new THREE.Mesh(geo, bodyMat));
          // Underside darker
          const geo2 = geo.clone();
          if(side>0) geo2.setIndex([0,1,2, 2,1,3, 2,3,4, 4,3,5]);
          else        geo2.setIndex([0,2,1, 2,3,1, 2,4,3, 4,5,3]);
          geo2.computeVertexNormals();
          grp.add(new THREE.Mesh(geo2, darkMat));
        });

        // ── All-moving horizontal tails (small, behind wings) ──
        [-1,1].forEach(side=>{
          const geo = new THREE.BufferGeometry();
          const x = side;
          const v = sv([
            x*0.58,  0.0,  1.2,
            x*0.58,  0.0,  2.0,
            x*1.8,  -0.04, 1.5,
            x*1.7,  -0.04, 2.1,
          ]);
          geo.setAttribute('position', new THREE.BufferAttribute(v,3));
          if(side>0) geo.setIndex([0,2,1, 2,3,1]);
          else        geo.setIndex([0,1,2, 2,1,3]);
          geo.computeVertexNormals();
          grp.add(new THREE.Mesh(geo, darkMat));
        });

        // ── Twin canted vertical tails (~27° outward cant) ──
        [-0.5, 0.5].forEach(x=>{
          const side = x>0?1:-1;
          const geo = new THREE.BufferGeometry();
          const v = sv([
            x,          0.0,  0.8,
            x,          0.0,  1.9,
            x+side*0.3, 1.1,  1.0,
            x+side*0.28,1.0,  1.85,
          ]);
          geo.setAttribute('position', new THREE.BufferAttribute(v,3));
          geo.setIndex([0,1,3, 0,3,2, 0,2,3, 0,3,1]);
          geo.computeVertexNormals();
          grp.add(new THREE.Mesh(geo, darkMat));
        });

        // ── Rectangular 2D TVC nozzles side by side ──
        [-0.5, 0.5].forEach(x=>{
          const noz = new THREE.Mesh(
            new THREE.BoxGeometry(S*0.38, S*0.22, S*0.5),
            darkMat
          );
          noz.position.set(x*S, -0.06*S, 2.25*S);
          grp.add(noz);
          const glow = new THREE.Mesh(
            new THREE.BoxGeometry(S*0.28, S*0.16, S*0.08),
            glowMat
          );
          glow.position.set(x*S, -0.06*S, 2.52*S);
          grp.add(glow);
        });

        // ── Long bubble canopy ──
        const canopy = new THREE.Mesh(
          new THREE.SphereGeometry(S*0.2, 8, 6, 0, Math.PI*2, 0, Math.PI*0.55),
          glassMat
        );
        canopy.scale.set(1, 0.65, 2.8);
        canopy.position.set(0, S*0.22, -S*1.2);
        grp.add(canopy);

        return grp;
      }
      function mkJetMissileMesh(){
        const grp = new THREE.Group();
        const mat = new THREE.MeshPhongMaterial({color:0xdddd00, emissive:0x886600, shininess:60});
        const body = new THREE.Mesh(new THREE.CylinderGeometry(0.05,0.06,0.45,5), mat);
        grp.add(body);
        const nose = new THREE.Mesh(new THREE.CylinderGeometry(0,0.05,0.18,5), mat);
        nose.position.y = 0.31;
        grp.add(nose);
        return grp;
      }

      // Initialize airbases on globe
      US_AIRBASES.forEach(ab=>{
        ab.vec = ll2v(ab.lat, ab.lng);
        const n = ab.vec.clone().normalize();
        // Runway pad
        const padMat = new THREE.MeshPhongMaterial({color:0x444433, shininess:5});
        const pad = new THREE.Mesh(new THREE.BoxGeometry(3.5,0.15,1.2), padMat);
        pad.position.copy(n.clone().multiplyScalar(GLOBE_R+0.1));
        pad.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), n);
        G.add(pad);
        // US flag marker
        const markerMat = new THREE.MeshBasicMaterial({color:0x3355aa});
        const marker = new THREE.Mesh(new THREE.SphereGeometry(0.6,6,6), markerMat);
        marker.position.copy(n.clone().multiplyScalar(GLOBE_R+0.8));
        G.add(marker);
        // Small 🇺🇸 label via sprite
        const fc = document.createElement('canvas'); fc.width=64; fc.height=64;
        const ctx = fc.getContext('2d');
        ctx.font='36px serif'; ctx.textAlign='center'; ctx.textBaseline='middle';
        ctx.fillText('🇺🇸',32,32);
        const tex = new THREE.CanvasTexture(fc);
        const spr = new THREE.Sprite(new THREE.SpriteMaterial({map:tex,transparent:true}));
        spr.scale.set(5,5,1);
        spr.position.copy(n.clone().multiplyScalar(GLOBE_R+4));
        G.add(spr);
      });

      function mkJet(airbase, targetBearIdx, formationOffset){
        const bi = targetBearIdx;
        const target = BEARS[bi];
        // Spawn on the runway at surface level
        const surfacePos = airbase.vec.clone().normalize().multiplyScalar(GLOBE_R + 0.5);
        // Formation offset perpendicular to flight direction, on the surface
        const toTarget = target.vec.clone().sub(airbase.vec).normalize();
        const up = surfacePos.clone().normalize();
        const right = new THREE.Vector3().crossVectors(toTarget, up).normalize();
        const spawnPos = surfacePos.clone().addScaledVector(right, formationOffset * 2.5);

        const mesh = mkF22Mesh();
        const trail = mkTrail(0xaaccff, 0.5);
        mesh.position.copy(spawnPos);
        G.add(mesh);

        // Initial velocity: along runway toward target direction, tangent to surface
        const n = spawnPos.clone().normalize();
        const tNorm = target.vec.clone().normalize();
        let vel = tNorm.clone().sub(n.clone().multiplyScalar(n.dot(tNorm)));
        if(vel.length() < 0.001) vel.set(1,0,0);
        vel.normalize();

        // Cruise waypoint: JET_ALT above airbase, offset in flight direction
        const cruiseWaypoint = airbase.vec.clone().normalize().multiplyScalar(GLOBE_R + JET_ALT)
          .addScaledVector(vel, 18);

        return {
          id: midCounter++,
          pos: spawnPos.clone(),
          vel: vel.clone(),
          targetBearIdx: bi,
          targetPos: target.vec.clone(),
          airbasePos: airbase.vec.clone().normalize().multiplyScalar(GLOBE_R + JET_ALT),
          cruiseWaypoint,
          dead: false,
          mesh, trail,
          state: 'takeoff', // 'takeoff' | 'inbound' | 'returning' | 'landing'
          missilesLaunched: false,
          frameCount: 0,
          distToTarget(){ return this.pos.distanceTo(this.targetPos); }
        };
      }

      function mkJetMissile(jetPos, targetBearIdx){
        const aliveBears = BEARS.filter((_,i)=>siteHpRef[i]>0);
        const target = aliveBears.length>0
          ? aliveBears[Math.floor(Math.random()*aliveBears.length)]
          : BEARS[Math.floor(Math.random()*BEARS.length)];
        const tBi = BEARS.indexOf(target);
        const mesh = mkJetMissileMesh();
        const trail = mkTrail(0xffdd00, 0.6);
        mesh.position.copy(jetPos);
        G.add(mesh);
        const n = jetPos.clone().normalize();
        const tNorm = target.vec.clone().normalize();
        let vel = tNorm.clone().sub(n.clone().multiplyScalar(n.dot(tNorm)));
        if(vel.length() < 0.001) vel.set(1,0,0);
        vel.normalize();
        return {
          id: midCounter++,
          pos: jetPos.clone(),
          vel: vel.clone(),
          targetPos: target.vec.clone().normalize().multiplyScalar(GLOBE_R),
          targetBearIdx: tBi,
          dead: false, mesh, trail,
          frameCount: 0,
          age: 0,
          startNorm: jetPos.clone().normalize(),
          targetNorm: target.vec.clone().normalize(),
          distToTarget(){ return this.pos.distanceTo(this.targetPos); }
        };
      }

      function fireJets(waveN){
        if(!JET_WAVES.has(waveN)) return;
        // Distribute 5 jets across 3 bases: 2, 2, 1
        const dist = [2, 2, 1];
        const offsets = [[-1,0], [1,0], [-1,0],[1,0], [0]]; // formation offsets per base
        let jetIdx = 0;
        dist.forEach((count, abIdx)=>{
          const ab = US_AIRBASES[abIdx];
          const targetBi = Math.floor(Math.random()*BEARS.length);
          for(let k=0; k<count; k++){
            const offset = offsets[jetIdx][k] !== undefined ? offsets[jetIdx][k] : (k-0.5);
            jets.push(mkJet(ab, targetBi, offset));
            jetIdx++;
          }
        });
      }

      function checkJetRadar(){
        const allTargets = [...jets, ...jetMissiles];
        allTargets.forEach(t=>{
          if(t.dead) return;
          BEARS.forEach((bear,bi)=>{
            if(siteHpRef[bi]<=0) return;
            const key=`jet-${bi}-${t.id}`;
            if(detectionLog.has(key)) return;
            if(t.pos.distanceTo(bear.vec)<RADAR_RANGE){
              detectionLog.add(key);
              bearRadars[bi].pulseRings.forEach((r,k)=>{r.age=k*8;});
              setTimeout(()=>{
                if(t.dead || siteHpRef[bi]<=0) return;
                const siteCounts = [0,0,0,0,0];
                const coverage = new Map();
                icepts.forEach(iv=>{
                  if(iv.dead) return;
                  siteCounts[iv.bearIdx]++;
                  coverage.set(iv.target.id, (coverage.get(iv.target.id)||0)+1);
                });
                if(siteCounts[bi] >= MAX_ICEPT_PER_SITE) return;
                if((coverage.get(t.id)||0) >= MAX_ICEPT_PER_MISSILE) return;
                icepts.push(mkIcept(bear, t, bi));
              }, DETECT_DELAY / speedRef.current);
            }
          });
        });
      }

      // ── MISSILE (velocity-steered, evasive) ───────────────
      function mkMissileMesh(){
        const grp = new THREE.Group();
        const mat = new THREE.MeshPhongMaterial({color:0xff2200, emissive:0x880000, shininess:40});
        // Body — slimmer and shorter
        const body = new THREE.Mesh(new THREE.CylinderGeometry(0.35,0.4,2.8,6), mat);
        grp.add(body);
        // Nose cone — tighter point
        const nose = new THREE.Mesh(new THREE.CylinderGeometry(0,0.35,1.2,6), mat);
        nose.position.y = 2.0;
        grp.add(nose);
        // Two small fins only — barely visible at this scale, just enough shape
        const finMat = new THREE.MeshPhongMaterial({color:0xcc1100,emissive:0x440000});
        for(let i=0;i<2;i++){
          const fin = new THREE.Mesh(new THREE.BoxGeometry(0.08,0.9,0.5), finMat);
          fin.position.y = -1.1;
          fin.rotation.y = i*Math.PI/2;
          fin.position.x = Math.cos(i*Math.PI/2)*0.4;
          fin.position.z = Math.sin(i*Math.PI/2)*0.4;
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
        // Initial velocity: great-circle tangent toward target (stable for any lat/lng pair)
        const n=startPos.clone().normalize();
        const tNorm=targetPos.clone().normalize();
        let gcTangent=tNorm.clone().sub(n.clone().multiplyScalar(n.dot(tNorm)));
        if(gcTangent.length()<0.001){
          // Antipodal edge case — pick any perpendicular
          gcTangent=new THREE.Vector3(1,0,0).cross(n);
          if(gcTangent.length()<0.001) gcTangent=new THREE.Vector3(0,1,0).cross(n);
        }
        const tangent=gcTangent.normalize();
        const mesh=mkMissileMesh();
        const trail=mkTrail(0xccbbaa,0.55);
        mesh.position.copy(startPos);G.add(mesh);
        launched++;
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
      function mkIceptMesh(){
        const grp = new THREE.Group();
        const mat = new THREE.MeshPhongMaterial({color:0xddeeff, emissive:0x224466, shininess:80});
        const body = new THREE.Mesh(new THREE.CylinderGeometry(0.12,0.14,0.95,6), mat);
        grp.add(body);
        const nose = new THREE.Mesh(new THREE.CylinderGeometry(0,0.12,0.45,6), mat);
        nose.position.y = 0.7;
        grp.add(nose);
        const finMat = new THREE.MeshPhongMaterial({color:0xaaccee, emissive:0x112233});
        for(let i=0;i<2;i++){
          const fin = new THREE.Mesh(new THREE.BoxGeometry(0.03,0.32,0.18), finMat);
          fin.position.y = -0.38;
          fin.rotation.y = i*Math.PI/2;
          fin.position.x = Math.cos(i*Math.PI/2)*0.15;
          fin.position.z = Math.sin(i*Math.PI/2)*0.15;
          grp.add(fin);
        }
        return grp;
      }

      function mkIcept(bearSite, target, bi){
        iceptLaunched++;
        const mesh = mkIceptMesh();
        const trail = mkTrail(0x00aaff, 0.7);
        const launchPos = bearSite.vec.clone().normalize().multiplyScalar(GLOBE_R + 1.5);
        mesh.position.copy(launchPos); G.add(mesh);
        spawnBeam(bearSite.vec);
        const track = { pos: target.pos.clone(), vel: target.vel.clone(), age: 0, altVel: 0 };
        // Initial velocity: lead the missile rather than aiming at current position
        // Simple 1-step estimate — how long to reach target, where will it be by then?
        const distToTarget = launchPos.distanceTo(target.pos);
        const travelFrames = Math.min(distToTarget / ICEPT_SPEED, 60); // cap lead at 60 frames
        const leadPos = target.pos.clone().addScaledVector(target.vel, travelFrames * MISSILE_SPEED);
        leadPos.normalize().multiplyScalar(target.pos.length()); // keep on same altitude shell
        let initVel = leadPos.sub(launchPos);
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
                // Build counts once — single pass over interceptors
                const siteCounts = [0,0,0,0,0];
                const missileCoverage = new Map();
                icepts.forEach(iv=>{
                  if(iv.dead) return;
                  siteCounts[iv.bearIdx]++;
                  const mid = iv.target.id;
                  missileCoverage.set(mid, (missileCoverage.get(mid)||0) + 1);
                });
                // Per-site limit
                if(siteCounts[bi] >= MAX_ICEPT_PER_SITE) return;
                // Global per-missile limit
                if((missileCoverage.get(m.id)||0) >= MAX_ICEPT_PER_MISSILE) return;

                // Candidates in radar range with capacity
                const candidates = missiles.filter(cand=>{
                  if(cand.dead) return false;
                  if(cand.pos.distanceTo(bear.vec) >= RADAR_RANGE) return false;
                  if((missileCoverage.get(cand.id)||0) >= MAX_ICEPT_PER_MISSILE) return false;

                  return true;
                });

                if(candidates.length === 0) return;

                // Sort by urgency (closest to target) then by coverage as tiebreaker
                candidates.sort((a,b)=>{
                  const covA = missileCoverage.get(a.id)||0;
                  const covB = missileCoverage.get(b.id)||0;
                  if(covA !== covB) return covA - covB; // unassigned first
                  // tiebreak: most urgent (least distance remaining to target)
                  return a.pos.distanceTo(a.targetPos) - b.pos.distanceTo(b.targetPos);
                });

                icepts.push(mkIcept(bear, candidates[0], bi));
              }, DETECT_DELAY / speedRef.current);
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
        // Wave size: 15 missiles, +2 every 3 waves, caps at 35
        const waveSize = Math.min(35, 15 + Math.floor((waveNum - 1) / 3) * 2);
        const spread = 500; // ms between individual launches within wave
        for(let i = 0; i < waveSize; i++){
          setTimeout(launch, (i * spread + Math.random() * 150) / speedRef.current);
        }
        // Jets launch with the wave (waves 5,6,8,9,10)
        if(JET_WAVES.has(waveNum)) setTimeout(()=>fireJets(waveNum), 1200/speedRef.current);
        // Gap between waves: steady 10s regardless of wave number
        const nextGap = 10000 / speedRef.current;
        if(waveNum >= 10){
          // Bears survived all 10 waves — bears win after last missiles clear
          waveTimeout = setTimeout(()=>{
            // Wait for remaining missiles to resolve (up to 30s), then declare bear victory
            const checkClear = setInterval(()=>{
              if(missiles.length === 0 && jets.length === 0 && jetMissiles.length === 0){
                clearInterval(checkClear);
                if(gameOverFired.current) return;
                gameOverFired.current = true;
                cancelAnimationFrame(animId);
                setTimeout(()=>{
                  const report = {
                    launched, impacts, iceptLaunched, intercepted,
                    waves: waveNum, timestamp: Date.now(), bearsWin: true,
                      fpsLog: [...fpsLogRef.current]
                  };
                  setGameOver(report);
                  onGameOver(report);
                }, 1500/speedRef.current);
              }
            }, 500/speedRef.current);
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
          camera.position.z=Math.max(150,Math.min(1800,camera.position.z*(pinchD/d)));
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
        camera.position.z=Math.max(150,Math.min(1800,camera.position.z*(1+e.deltaY*0.0008)));
      },{passive:false});

      let frame=0;
      function animateStep(){
        frame++;
        if(frame%30===0){
          const now=performance.now();
          if(animate._lastT){ const f=Math.round(30000/(now-animate._lastT)); setFps(f); fpsLogRef.current.push(f); }
          animate._lastT=now;
        }

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

          // ── Ballistic arc — no steering advantage in terminal ──────────
          const MISSILE_MAX_TURN = 0.042;
          const steerStrength = m.curving ? 0.006 : MISSILE_MAX_TURN;
          m.vel = steerVel(m.pos, m.vel, m.targetPos, steerStrength);

          const startAngle2 = m.startNorm.angleTo(m.targetNorm);
          const curAngle2   = m.startNorm.angleTo(m.pos.clone().normalize());
          const progress2   = startAngle2 > 0.001 ? Math.min(1, curAngle2 / startAngle2) : 1;

          // Arc altitude: sin curve that goes cleanly to 0 at impact
          // No clamp — let it reach 0 so missile dives into surface naturally
          const APEX = 72;
          const arcAlt = APEX * Math.sin(progress2 * Math.PI);

          // In descent phase (progress > 0.5), blend in a radially inward velocity
          // component proportional to how fast altitude is dropping.
          // This tilts the missile nose-down without any steering advantage —
          // it's pure physics: gravity pulling the warhead in.
          const descentBlend = Math.max(0, (progress2 - 0.5) / 0.5); // 0 at apex, 1 at impact
          const inward = m.pos.clone().normalize().multiplyScalar(-descentBlend * 0.35);

          const moved = moveOnSphere(m.pos, m.vel, MISSILE_SPEED, Math.max(0, arcAlt));
          m.pos = moved.pos.clone().addScaledVector(inward, MISSILE_SPEED);
          m.vel = moved.vel;

          // Keep missile above surface until it hits
          const r = m.pos.length();
          if(r < GLOBE_R + 0.5) m.pos.normalize().multiplyScalar(GLOBE_R + 0.5);

          m.mesh.position.copy(m.pos);
          // Orient nose along combined velocity + inward for visual dive angle
          const orientDir = m.vel.clone().add(inward).normalize();
          if(orientDir.length()>0.001) m.mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), orientDir);
          m.trail.add(m.pos);

          // Impact check — tighter radius, only triggers near surface
          const distToTarget=m.distToTarget();
          if(distToTarget<SITE_HIT_DIST){
            explode(m.pos.clone(),0xff2200,1.8);
            G.remove(m.mesh);m.trail.dispose();m.dead=true;
            const bi=m.targetBearIdx;
            if(siteHpRef[bi]>0){
              siteHpRef[bi]--;updateSiteVisual(bi);
              if(siteHpRef[bi]===0){
                explode(BEARS[bi].vec.clone().normalize().multiplyScalar(GLOBE_R+FLY_ALT),0xff4400,2.5);
                // Check if ALL bases are destroyed
                if(!gameOverFired.current && siteHpRef.every(hp=>hp<=0)){
                  gameOverFired.current = true;
                  clearTimeout(waveTimeout);
                  cancelAnimationFrame(animId);
                  setTimeout(()=>{
                    const report = {
                      launched, impacts, iceptLaunched, intercepted,
                      waves: waveNum,
                      timestamp: Date.now(),
                      fpsLog: [...fpsLogRef.current]
                    };
                    setGameOver(report);
                    onGameOver(report);
                  }, 2000/speedRef.current);
                }
              }
            }
            impacts++;missiles.splice(i,1);
          } else if(m.frameCount>3600){
            // Very old missile — detonate it where it is, count as miss (no HP damage)
            explode(m.pos.clone(),0xff6600,0.9);
            G.remove(m.mesh);m.trail.dispose();m.dead=true;missiles.splice(i,1);
          }
        }

        if(frame%15===0){ checkRadar(); checkJetRadar(); }

        // ── Jets ──────────────────────────────────────────────
        for(let i=jets.length-1;i>=0;i--){
          const j=jets[i];
          if(j.dead){ G.remove(j.mesh); j.trail.dispose(); jets.splice(i,1); continue; }
          j.frameCount++;

          if(j.state==='takeoff'){
            // Shallow climb — ramp altitude up gradually while flying toward target
            const curAlt = j.pos.length() - GLOBE_R;
            const climbAlt = Math.min(JET_ALT, curAlt + 0.4);
            j.vel = steerVel(j.pos, j.vel, j.targetPos, 0.04);
            const climbMoved = moveOnSphere(j.pos, j.vel, JET_SPEED, climbAlt);
            j.pos = climbMoved.pos; j.vel = climbMoved.vel;
            if(climbAlt >= JET_ALT * 0.95) j.state = 'inbound';
          } else if(j.state==='inbound'){
            j.vel = steerVel(j.pos, j.vel, j.targetPos, 0.055);
            const moved = moveOnSphere(j.pos, j.vel, JET_SPEED, JET_ALT);
            j.pos = moved.pos; j.vel = moved.vel;

            if(!j.missilesLaunched && j.pos.distanceTo(j.targetPos) < JET_LAUNCH_RANGE){
              j.missilesLaunched = true;
              for(let m=0;m<3;m++) jetMissiles.push(mkJetMissile(j.pos.clone(), j.targetBearIdx));
              j.state = 'returning';
              const n2 = j.pos.clone().normalize();
              let retVel = j.airbasePos.clone().sub(j.pos).normalize();
              retVel = retVel.sub(n2.clone().multiplyScalar(n2.dot(retVel)));
              if(retVel.length()<0.001) retVel.set(1,0,0);
              j.vel = retVel.normalize();
            }
          } else if(j.state==='returning'){
            j.vel = steerVel(j.pos, j.vel, j.airbasePos, 0.055);
            const moved = moveOnSphere(j.pos, j.vel, JET_SPEED, JET_ALT);
            j.pos = moved.pos; j.vel = moved.vel;
            if(j.pos.distanceTo(j.airbasePos) < 25) j.state = 'landing';
          } else {
            // Landing: shallow descent — bleed altitude gradually while flying to airbase
            const curAlt2 = j.pos.length() - GLOBE_R;
            const descentAlt = Math.max(0.5, curAlt2 - 0.4);
            j.vel = steerVel(j.pos, j.vel, j.airbasePos, 0.055);
            const landMoved = moveOnSphere(j.pos, j.vel, JET_SPEED, descentAlt);
            j.pos = landMoved.pos; j.vel = landMoved.vel;
            if(descentAlt <= 0.5 || j.pos.distanceTo(j.airbasePos.clone().normalize().multiplyScalar(GLOBE_R+0.5)) < 5){
              G.remove(j.mesh); j.trail.dispose(); j.dead=true; jets.splice(i,1); continue;
            }
          }

          j.mesh.position.copy(j.pos);
          const jFwd = j.vel.clone().normalize();
          const jUp2 = j.pos.clone().normalize();
          const jRight = new THREE.Vector3().crossVectors(jFwd, jUp2).normalize();
          const jTrueUp = new THREE.Vector3().crossVectors(jRight, jFwd).normalize();
          const jMat = new THREE.Matrix4().makeBasis(jRight, jTrueUp, jFwd.clone().negate());
          j.mesh.quaternion.setFromRotationMatrix(jMat);
          j.trail.add(j.pos);
        }

        // ── Jet Missiles ──────────────────────────────────────
        for(let i=jetMissiles.length-1;i>=0;i--){
          const jm=jetMissiles[i];
          if(jm.dead){ G.remove(jm.mesh); jm.trail.dispose(); jetMissiles.splice(i,1); continue; }
          jm.frameCount++; jm.age++;

          // Dive in 3D toward the bear base surface point — no altitude lock
          const jmAim = BEARS[jm.targetBearIdx].vec.clone().normalize().multiplyScalar(GLOBE_R + 0.5);
          const jmMoved = steerInterceptor(jm.pos, jm.vel, jmAim, JET_MISSILE_SPEED);
          jm.pos = jmMoved.pos; jm.vel = jmMoved.vel;

          jm.mesh.position.copy(jm.pos);
          if(jm.vel.length()>0.001) jm.mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), jm.vel.clone().normalize());
          jm.trail.add(jm.pos);

          if(jm.age > JET_MISSILE_MAX_AGE){
            explode(jm.pos.clone(),0xffaa00,0.6);
            G.remove(jm.mesh); jm.trail.dispose(); jm.dead=true; jetMissiles.splice(i,1); continue;
          }

          // Hit check: direct 3D distance to surface target
          const jmDist = jm.pos.distanceTo(jmAim);
          if(jmDist < SITE_HIT_DIST){
            explode(jm.pos.clone(),0xffcc00,1.6);
            G.remove(jm.mesh); jm.trail.dispose(); jm.dead=true;
            const bi = jm.targetBearIdx;
            if(siteHpRef[bi]>0){
              siteHpRef[bi]--; updateSiteVisual(bi);
              impacts++;
              if(siteHpRef[bi]===0){
                explode(BEARS[bi].vec.clone().normalize().multiplyScalar(GLOBE_R+FLY_ALT),0xff4400,2.5);
                if(!gameOverFired.current && siteHpRef.every(hp=>hp<=0)){
                  gameOverFired.current = true;
                  clearTimeout(waveTimeout);
                  cancelAnimationFrame(animId);
                  setTimeout(()=>{
                    const report={launched,impacts,iceptLaunched,intercepted,waves:waveNum,timestamp:Date.now(),fpsLog:[...fpsLogRef.current]};
                    setGameOver(report); onGameOver(report);
                  },2000/speedRef.current);
                }
              }
            }
            jetMissiles.splice(i,1); continue;
          }
        }

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
            // Find nearest alive threat (missiles, jets, jet missiles)
            let nearest=null, nearDist=Infinity;
            [...missiles, ...jets, ...jetMissiles].forEach(m2=>{ if(!m2.dead){ const d=iv.pos.distanceTo(m2.pos); if(d<nearDist){nearDist=d;nearest=m2;} } });
            if(nearest){
              // Reroute: seed track with noise — interceptor doesn't get free perfect data
              iv.target = nearest;
              const noiseDir = new THREE.Vector3(Math.random()-0.5,Math.random()-0.5,Math.random()-0.5).normalize();
              iv.track = {
                pos: nearest.pos.clone().addScaledVector(noiseDir, 3+Math.random()*5),
                vel: nearest.vel.clone().add(new THREE.Vector3((Math.random()-0.5)*0.08,(Math.random()-0.5)*0.08,(Math.random()-0.5)*0.08)).normalize(),
                age: 15, // treat as slightly stale from the start
                altVel: 0
              };
              iv.trackAge = 0;
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
          // Radar update every 30 frames — phased array rate
          iv.track.age = (iv.track.age||0) + 1;
          if(iv.trackAge%30===0){
            // Use last known track position — not live missile position (no cheating)
            const bearIdx = BEARS.findIndex(b=>b.vec && iv.track.pos.distanceTo(b.vec)<RADAR_RANGE);
            if(bearIdx>=0 && siteHpRef[bearIdx]>0){
              const oldAlt = iv.track.pos.length() - GLOBE_R;
              const noiseDir = new THREE.Vector3(Math.random()-0.5,Math.random()-0.5,Math.random()-0.5).normalize();
              iv.track.pos = iv.target.pos.clone().addScaledVector(noiseDir, 2+Math.random()*3);
              iv.track.vel = iv.target.vel.clone()
                .add(new THREE.Vector3((Math.random()-0.5)*0.06,(Math.random()-0.5)*0.06,(Math.random()-0.5)*0.06))
                .normalize();
              // Arc-aware: observe altitude trend between radar pings
              const newAlt = iv.track.pos.length() - GLOBE_R;
              iv.track.altVel = (newAlt - oldAlt) / 30; // altitude change per frame
              iv.track.age = 0; // reset staleness on fresh update
            }
          }
          // Terminal seeker: within 25 units, ditch the stale track and home directly
          // This prevents misses caused by chasing a now-wrong lead point at close range
          const terminalDist = iv.pos.distanceTo(iv.target.pos);
          let aim;
          if(terminalDist < 25){
            // Direct pursuit — interceptor "sees" the missile on its own seeker
            aim = iv.target.pos.clone();
          } else {
            aim=computeIntercept(iv.pos,iv.vel,iv.track);
          }
          // Interceptor climbs from ground, tracks missile altitude
          // True 3D steering — no altitude argument, no speed burst
          const moved=steerInterceptor(iv.pos,iv.vel,aim,ICEPT_SPEED);
          if(!isNaN(moved.pos.x)){ iv.pos=moved.pos; iv.vel=moved.vel; }
          iv.mesh.position.copy(iv.pos);
          // Orient interceptor nose along velocity
          const iUp = iv.vel.clone().normalize();
          if(iUp.length()>0.001) iv.mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0), iUp);
          iv.trail.add(iv.pos);
          if(iv.pos.distanceTo(iv.target.pos)<HIT_DIST){
            explode(iv.pos.clone(),0x00ddff,1.1);
            iv.target.dead=true;G.remove(iv.target.mesh);iv.target.trail.dispose();
            G.remove(iv.mesh);iv.trail.dispose();iv.dead=true;
            intercepted++;
            // Jets and jet missiles earn an immediate repair — they're harder targets
            const isJetTarget = jets.includes(iv.target);
            if(isJetTarget){
              setTimeout(tryRepair, 1500/speedRef.current);
            } else {
              interceptSinceRepair++;
              if(interceptSinceRepair>=REPAIR_EVERY){interceptSinceRepair=0;setTimeout(tryRepair,1500/speedRef.current);}
            }
            icepts.splice(i,1);
          }
        }

        // Explosions
        for(let i=exps.length-1;i>=0;i--){const e=exps[i];e.age++;const p=e.age/e.max;e.fl.material.opacity=Math.max(0,0.9-p*5);e.fl.scale.setScalar(1+p*3);e.parts.forEach(({m,vel})=>{m.position.addScaledVector(vel,1);vel.multiplyScalar(0.91);m.material.opacity=Math.max(0,1-p*1.6);m.scale.setScalar(Math.max(0.01,(1-p*0.8)*e.sz));});if(e.age>=e.max){G.remove(e.grp);exps.splice(i,1);}}

        for(let i=beams.length-1;i>=0;i--){const b=beams[i];b.age++;b.mat.opacity=Math.max(0,1-b.age/b.max);if(b.age>=b.max){G.remove(b.line);beams.splice(i,1);}}

        if(frame%2===0){
          const t=Date.now()*0.003;

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
          // Realistic wind — multi-harmonic travelling wave
          flags.forEach(f=>{
            const pos = f.posAttr;
            const t = frame * 0.055;
            const gust = 0.75 + 0.25 * Math.sin(t * 0.11 + f.phase * 0.7);
            for(let vi=0;vi<pos.count;vi++){
              const u = (pos.getX(vi) + f.FW*0.5) / f.FW;
              const v = pos.getY(vi) / (f.FH*0.5);
              const amp = u * u * gust;
              const w1 = Math.sin(t * 1.0 - u * 5.2 + f.phase) * 0.65;
              const w2 = Math.sin(t * 2.1 - u * 9.8 + f.phase * 1.3) * 0.18;
              const vFactor = 1.0 + v * 0.12;
              const wave = (w1 + w2) * amp * vFactor;
              const droop = (0.5 - v * 0.5) * u * 0.12;
              pos.setZ(vi, wave);
              pos.setY(vi, f.restY[vi] - droop);
            }
            pos.needsUpdate = true;
          });
        }

        if(frame%30===0)setStats({l:launched,i:intercepted,h:impacts,a:missiles.length,w:waveNum,il:iceptLaunched});
      }
      function animate(){
        animId=requestAnimationFrame(animate); animIdRef.current=animId;
        if(pausedRef.current){ renderer.render(scene,camera); return; }
        const steps=speedRef.current;
        for(let s=0;s<steps;s++) animateStep();
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
        <div style={{display:"flex",justifyContent:"space-between",alignItems:"baseline",marginBottom:6}}>
          <div style={{color:"#fff",fontSize:14,fontWeight:"bold"}}>❄️ Cold War</div>
          <div style={{color:fps>=50?"#4ade80":fps>=30?"#facc15":"#f87171",fontSize:11,fontFamily:"'Courier New',monospace"}}>{fps} fps</div>
        </div>
        <div style={{display:"flex",gap:14,fontSize:12,color:"#aaa",marginBottom:6}}>
          <span>Launched <b style={{color:"#fff"}}>{stats.l}</b></span>
          <span>Intercepted <b style={{color:"#22d3ee"}}>{stats.i}</b></span>
          <span>Impacts <b style={{color:"#f87171"}}>{stats.h}</b></span>
          <span>Active <b style={{color:"#facc15"}}>{stats.a}</b></span>
          <span>Wave <b style={{color:"#c084fc"}}>{stats.w}</b></span>
        </div>
        <div style={{display:"flex",gap:8,alignItems:"center"}}>
          {siteHp.map((hp,i)=>(
            <div key={i} style={{display:"flex",flexDirection:"column",alignItems:"center",gap:2}}>
              <div style={{fontSize:10,color:"#aaa"}}>B{i+1}</div>
              <div style={{display:"flex",gap:2}}>
                {[0,1,2].map(k=><div key={k} style={{width:6,height:6,borderRadius:"50%",background:k<hp?hpColor(hp):"#1a1a1a",boxShadow:k<hp?`0 0 4px ${hpColor(hp)}`:"none"}}/>)}
              </div>
            </div>
          ))}
          <div style={{fontSize:11,color:"#aaa",marginLeft:4}}>Base HP</div>
        </div>
      </div>
      <div style={{position:"absolute",bottom:0,left:0,right:0,height:50,background:"rgba(0,0,0,0.85)",display:"flex",alignItems:"center",justifyContent:"center",gap:10,zIndex:10}}>
          {/* Pause / Resume */}
          <button
            onClick={()=>{ const next=!paused; setPaused(next); pausedRef.current=next; }}
            style={{padding:"7px 18px",background:"rgba(0,0,0,0.7)",
              border:paused?"1px solid #6aaa7a":"1px solid #555",
              color:paused?"#6aaa7a":"#aaa",
              fontFamily:"Georgia,serif",fontSize:12,cursor:"pointer",borderRadius:2}}
            onMouseEnter={e=>{e.currentTarget.style.borderColor=paused?"#8aca9a":"#888";e.currentTarget.style.color=paused?"#8aca9a":"#eee";}}
            onMouseLeave={e=>{e.currentTarget.style.borderColor=paused?"#6aaa7a":"#555";e.currentTarget.style.color=paused?"#6aaa7a":"#aaa";}}
          >{paused?"▶  Resume":"⏸  Pause"}</button>
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
        <div style={{position:"absolute",inset:0,background:"rgba(0,0,0,0.92)",display:"flex",alignItems:"center",justifyContent:"center",zIndex:50,padding:"16px",overflowY:"auto"}}>
          <div style={{fontFamily:"Georgia,'Times New Roman',serif",textAlign:"center",width:"100%",maxWidth:360}}>
            <div style={{fontSize:32,marginBottom:8}}>{gameOver.bearsWin?"🐻‍❄️":"💥"}</div>
            <div style={{fontSize:22,color:gameOver.bearsWin?"#6aaa7a":"#aa6a6a",marginBottom:4,fontWeight:"bold"}}>
              {gameOver.bearsWin?"Bears Win":"Defeat"}
            </div>
            <div style={{fontSize:12,color:"#666",marginBottom:16,fontStyle:"italic"}}>
              {gameOver.bearsWin?"All 10 waves survived":"All bear bases destroyed"} — Wave {gameOver.waves}
            </div>
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
                {(()=>{
                  const log = r.fpsLog || [];
                  if(log.length < 2) return null;
                  const sorted=[...log].sort((a,b)=>a-b);
                  const avg=Math.round(log.reduce((a,b)=>a+b,0)/log.length);
                  const median=sorted[Math.floor(sorted.length/2)];
                  const p1c=Math.max(1,Math.floor(sorted.length*0.01));
                  const p1=Math.round(sorted.slice(0,p1c).reduce((a,b)=>a+b,0)/p1c);
                  const mn=sorted[0], mx=sorted[sorted.length-1];
                  const W=300,H=50;
                  const tx=i=>Math.round(i/Math.max(log.length-1,1)*(W-2))+1;
                  const ty=v=>Math.round((1-(v-mn)/Math.max(mx-mn,1))*(H-4))+2;
                  const pts=log.map((v,i)=>`${tx(i)},${ty(v)}`).join(' ');
                  return(
                    <div style={{marginTop:8}}>
                      <svg width="100%" viewBox={`0 0 ${W} ${H}`} style={{display:"block",marginBottom:4}}>
                        <line x1="1" y1={ty(60)} x2={W-1} y2={ty(60)} stroke="#1a3a1a" strokeWidth="1" strokeDasharray="3,3"/>
                        <line x1="1" y1={ty(30)} x2={W-1} y2={ty(30)} stroke="#3a1a1a" strokeWidth="1" strokeDasharray="3,3"/>
                        <polyline points={pts} fill="none" stroke="#4ade80" strokeWidth="1.2" strokeLinejoin="round"/>
                      </svg>
                      <div style={{display:"flex",gap:10,fontSize:9,color:"#555"}}>
                        <span>avg <b style={{color:"#aaa"}}>{avg}</b></span>
                        <span>med <b style={{color:"#aaa"}}>{median}</b></span>
                        <span>1%low <b style={{color:"#f87171"}}>{p1}</b></span>
                        <span>min <b style={{color:"#aa6a6a"}}>{mn}</b></span>
                      </div>
                    </div>
                  );
                })()}
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
