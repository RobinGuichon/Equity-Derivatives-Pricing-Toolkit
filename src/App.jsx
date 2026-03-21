import Plot from 'react-plotly.js';
import React, { useState, useMemo, useEffect, useCallback } from "react";
import { LineChart, Line, BarChart, Bar, Cell, XAxis, YAxis, CartesianGrid, Tooltip, ResponsiveContainer, ReferenceLine } from "recharts";

// ─── MATH ────────────────────────────────────────────────────────────────────
function erf(x){const a=[.254829592,-.284496736,1.421413741,-1.453152027,1.061405429],p=.3275911,s=x<0?-1:1;x=Math.abs(x);const t=1/(1+p*x);return s*(1-((((a[4]*t+a[3])*t+a[2])*t+a[1])*t+a[0])*t*Math.exp(-x*x));}
const Phi=x=>0.5*(1+erf(x/Math.SQRT2));
const phi=x=>Math.exp(-.5*x*x)/Math.sqrt(2*Math.PI);

function bs(S,K,T,r,q,σ,put){
  if(T<=0||S<=0)return Math.max(put?K-S:S-K,0);
  const sq=Math.sqrt(T),d1=(Math.log(S/K)+(r-q+.5*σ*σ)*T)/(σ*sq),d2=d1-σ*sq,e=Math.exp(-r*T),eq=Math.exp(-q*T);
  return put?K*e*Phi(-d2)-S*eq*Phi(-d1):S*eq*Phi(d1)-K*e*Phi(d2);
}

function bsGreeks(S,K,T,r,q,σ,put){
  if(T<=0||S<=0)return{delta:put?-1:1,gamma:0,theta:0,vega:0,rho:0,vanna:0,vomma:0,charm:0,speed:0,veta:0,price:0};
  const sq=Math.sqrt(T),d1=(Math.log(S/K)+(r-q+.5*σ*σ)*T)/(σ*sq),d2=d1-σ*sq;
  const Nd1=Phi(d1),nd1=phi(d1),e=Math.exp(-r*T),eq=Math.exp(-q*T),vr=S*eq*nd1*sq;
  const price=put?K*e*Phi(-d2)-S*eq*Phi(-d1):S*eq*Phi(d1)-K*e*Phi(d2);
  const delta=put?eq*(Nd1-1):eq*Nd1,gamma=eq*nd1/(S*σ*sq);
  const theta=put?(-(S*eq*nd1*σ)/(2*sq)+r*K*e*Phi(-d2)-q*S*eq*Phi(-d1))/365:(-(S*eq*nd1*σ)/(2*sq)-r*K*e*Phi(d2)+q*S*eq*Nd1)/365;
  const vega=vr/100,rho=put?-K*T*e*Phi(-d2)/100:K*T*e*Phi(d2)/100;
  const vanna=-eq*nd1*d2/σ,vomma=(vr*d1*d2/σ)/100;
  const charm=put?(q*eq*Phi(-d1)-eq*nd1*(2*(r-q)*T-d2*σ*sq)/(2*T*σ*sq))/365:(q*eq*Nd1-eq*nd1*(2*(r-q)*T-d2*σ*sq)/(2*T*σ*sq))/365;
  const speed=-(gamma/S)*(d1/(σ*sq)+1);
  const veta=-(vr/100)*((r-q)*d1/(σ*sq)-(1+d1*d2)/(2*T))/365;
  return{price,delta,gamma,theta,vega,rho,vanna,vomma,charm,speed,veta};
}

// ─── RANDOM ────────────────────────────────────────────────────────────────
function lcg(seed){let s=seed>>>0;return()=>{s=(Math.imul(1664525,s)+1013904223)>>>0;return s/0x100000000;};}
function bm(u1,u2){return Math.sqrt(-2*Math.log(u1+1e-15))*Math.cos(2*Math.PI*u2);}
function genZ(nP,nS,seed=42){const r=lcg(seed),Z=[];for(let i=0;i<nP;i++){const p=[];for(let j=0;j<nS;j++)p.push(bm(r(),r()));Z.push(p);}return Z;}
function corrZ(Z1,Z2,rho){const sq=Math.sqrt(Math.max(1-rho*rho,0));return Z1.map((p,i)=>p.map((z,j)=>rho*z+sq*Z2[i][j]));}

// ─── PRICERS (all accept q) ────────────────────────────────────────────────
function binomAmer(S,K,T,r,q,σ,N,put){
  const dt=T/N,u=Math.exp(σ*Math.sqrt(dt)),d=1/u,p=(Math.exp((r-q)*dt)-d)/(u-d),disc=Math.exp(-r*dt);
  let V=Array.from({length:N+1},(_,i)=>Math.max(put?K-S*Math.pow(u,N-2*i):S*Math.pow(u,N-2*i)-K,0));
  for(let n=N-1;n>=0;n--)for(let i=0;i<=n;i++){const Sn=S*Math.pow(u,n-2*i);V[i]=Math.max(Math.max(put?K-Sn:Sn-K,0),disc*(p*V[i]+(1-p)*V[i+1]));}
  return V[0];
}

function binomBermudan(S,K,T,r,q,σ,N,put,nDates){
  const dt=T/N,u=Math.exp(σ*Math.sqrt(dt)),d=1/u,p=(Math.exp((r-q)*dt)-d)/(u-d),disc=Math.exp(-r*dt);
  let V=Array.from({length:N+1},(_,i)=>Math.max(put?K-S*Math.pow(u,N-2*i):S*Math.pow(u,N-2*i)-K,0));
  const interval=Math.max(1,Math.floor(N/nDates));
  for(let n=N-1;n>=0;n--){
    const canEx=(n%interval===0&&n>0);
    for(let i=0;i<=n;i++){
      const Sn=S*Math.pow(u,n-2*i);
      const cont=disc*(p*V[i]+(1-p)*V[i+1]);
      V[i]=canEx?Math.max(Math.max(put?K-Sn:Sn-K,0),cont):cont;
    }
  }
  return V[0];
}

function barrierMC(S0,K,T,r,q,σ,H,isDown,isOut,put,Z){
  const nS=Z[0].length,dt=T/nS,disc=Math.exp(-r*T),mu=(r-q-.5*σ*σ)*dt,v=σ*Math.sqrt(dt);
  let tot=0;
  for(const path of Z){let S=S0,hit=false;for(const z of path){S*=Math.exp(mu+v*z);if(isDown?S<=H:S>=H)hit=true;}if(isOut?!hit:hit)tot+=put?Math.max(K-S,0):Math.max(S-K,0);}
  return disc*tot/Z.length;
}

function digital(S,K,T,r,q,σ,isCall,isCash){
  if(T<=0)return isCall?(S>K?(isCash?1:S):0):(S<K?(isCash?1:S):0);
  const sq=Math.sqrt(T),d1=(Math.log(S/K)+(r-q+.5*σ*σ)*T)/(σ*sq),d2=d1-σ*sq,e=Math.exp(-r*T),eq=Math.exp(-q*T);
  return isCash?(isCall?e*Phi(d2):e*Phi(-d2)):(isCall?S*eq*Phi(d1):S*eq*Phi(-d1));
}

function lookbackMC(S0,K,T,r,q,σ,isFloat,put,Z){
  const nS=Z[0].length,dt=T/nS,disc=Math.exp(-r*T),mu=(r-q-.5*σ*σ)*dt,v=σ*Math.sqrt(dt);
  let tot=0;
  for(const path of Z){let S=S0,Smin=S0,Smax=S0;for(const z of path){S*=Math.exp(mu+v*z);if(S<Smin)Smin=S;if(S>Smax)Smax=S;}tot+=isFloat?(put?Smax-S:S-Smin):(put?Math.max(K-Smin,0):Math.max(Smax-K,0));}
  return disc*tot/Z.length;
}

function shoutMC(S0,K,T,r,q,σ,put,Z){
  const nS=Z[0].length,dt=T/nS,disc=Math.exp(-r*T),mu=(r-q-.5*σ*σ)*dt,v=σ*Math.sqrt(dt);
  let tot=0;
  for(const path of Z){let S=S0,floor=0;for(let j=0;j<nS;j++){S*=Math.exp(mu+v*path[j]);const tRem=T-(j+1)*dt;if(floor===0&&(put?S<K:S>K)&&tRem>dt){const atm=bs(S,S,tRem,r,q,σ,put);if((put?K-S:S-K)>=atm)floor=put?K-S:S-K;}}tot+=Math.max(put?Math.max(K-S,0):Math.max(S-K,0),floor);}
  return disc*tot/Z.length;
}

function asianMC(S0,K,T,r,q,σ,put,Z){
  const nS=Z[0].length,dt=T/nS,disc=Math.exp(-r*T),mu=(r-q-.5*σ*σ)*dt,v=σ*Math.sqrt(dt);
  let tot=0;
  for(const path of Z){let S=S0,avg=0;for(const z of path){S*=Math.exp(mu+v*z);avg+=S;}avg/=nS;tot+=put?Math.max(K-avg,0):Math.max(avg-K,0);}
  return disc*tot/Z.length;
}

function basketMC(S1,S2,K,T,r,q,σ1,σ2,rho,w1,put,Z1,Z2c){
  const nS=Z1[0].length,dt=T/nS,disc=Math.exp(-r*T),mu1=(r-q-.5*σ1*σ1)*dt,v1=σ1*Math.sqrt(dt),mu2=(r-q-.5*σ2*σ2)*dt,v2=σ2*Math.sqrt(dt);
  let tot=0;
  for(let i=0;i<Z1.length;i++){let A=S1,B=S2;for(let j=0;j<nS;j++){A*=Math.exp(mu1+v1*Z1[i][j]);B*=Math.exp(mu2+v2*Z2c[i][j]);}const bsk=w1*A+(1-w1)*B;tot+=put?Math.max(K-bsk,0):Math.max(bsk-K,0);}
  return disc*tot/Z1.length;
}

function rainbowMC(S1,S2,K,T,r,q,σ1,σ2,rho,type,Z1,Z2c){
  const nS=Z1[0].length,dt=T/nS,disc=Math.exp(-r*T),mu1=(r-q-.5*σ1*σ1)*dt,v1=σ1*Math.sqrt(dt),mu2=(r-q-.5*σ2*σ2)*dt,v2=σ2*Math.sqrt(dt);
  let tot=0;
  for(let i=0;i<Z1.length;i++){let A=S1,B=S2;for(let j=0;j<nS;j++){A*=Math.exp(mu1+v1*Z1[i][j]);B*=Math.exp(mu2+v2*Z2c[i][j]);}const best=Math.max(A,B),worst=Math.min(A,B);tot+=type==="best-call"?Math.max(best-K,0):type==="worst-call"?Math.max(worst-K,0):type==="best-put"?Math.max(K-best,0):Math.max(K-worst,0);}
  return disc*tot/Z1.length;
}

function chooserMC(S0,K,T,t0,r,q,σ,Z){
  const nS0=Math.round(Z[0].length*t0/T),dt=T/Z[0].length,mu=(r-q-.5*σ*σ)*dt,v=σ*Math.sqrt(dt);
  let tot=0;
  for(const path of Z){let S=S0;for(let j=0;j<nS0;j++)S*=Math.exp(mu+v*path[j]);tot+=Math.max(bs(S,K,T-t0,r,q,σ,false),bs(S,K,T-t0,r,q,σ,true));}
  return Math.exp(-r*t0)*tot/Z.length;
}

function cliquetMC(S0,T,r,q,σ,cap,floor,nPeriods,Z){
  const nS=Z[0].length,dt=T/nS,mu=(r-q-.5*σ*σ)*dt,v=σ*Math.sqrt(dt),disc=Math.exp(-r*T),spp=Math.floor(nS/nPeriods);
  let tot=0;
  for(const path of Z){let S=S0,payoff=0;for(let p=0;p<nPeriods;p++){const Sprev=S;for(let j=0;j<spp;j++)S*=Math.exp(mu+v*(path[p*spp+j]||0));payoff+=Math.min(Math.max((S-Sprev)/Sprev,floor),cap);}tot+=Math.max(payoff,0);}
  return disc*tot/Z.length;
}

function powerMC(S0,K,T,r,q,σ,n,put,Z){
  const nS=Z[0].length,dt=T/nS,disc=Math.exp(-r*T),mu=(r-q-.5*σ*σ)*dt,v=σ*Math.sqrt(dt);
  let tot=0;
  for(const path of Z){let S=S0;for(const z of path)S*=Math.exp(mu+v*z);tot+=put?Math.max(K-Math.pow(S,n),0):Math.max(Math.pow(S,n)-K,0);}
  return disc*tot/Z.length;
}

function margrabeP(S1,S2,T,r,σ1,σ2,rho){
  const σ=Math.sqrt(σ1*σ1+σ2*σ2-2*rho*σ1*σ2);
  if(σ<=0)return Math.max(S2-S1,0);
  const d1=(Math.log(S2/S1)+.5*σ*σ*T)/(σ*Math.sqrt(T)),d2=d1-σ*Math.sqrt(T);
  return S2*Phi(d1)-S1*Phi(d2);
}

function fwdStart(S0,alpha,T,t0,r,q,σ,put){return S0*Math.exp(-q*t0)*bs(1,alpha,T-t0,r,q,σ,put);}

function parisianMC(S0,K,T,r,q,σ,H,isDown,isOut,window,put,Z){
  const nS=Z[0].length,dt=T/nS,disc=Math.exp(-r*T),mu=(r-q-.5*σ*σ)*dt,v=σ*Math.sqrt(dt);
  const req=Math.max(1,Math.floor((window/365)/dt));
  let tot=0;
  for(const path of Z){
    let S=S0,cons=0,hit=false;
    for(const z of path){
      S*=Math.exp(mu+v*z);
      if(isDown?S<=H:S>=H){cons++;if(cons>=req){hit=true;break;}}else{cons=0;}
    }
    if(isOut?!hit:hit)tot+=put?Math.max(K-S,0):Math.max(S-K,0);
  }
  return disc*tot/Z.length;
}

function quantoBS(S,K,T,r,q,σ,σFX,rho,put){
  if(T<=0||S<=0)return Math.max(put?K-S:S-K,0);
  const q_adj=q+rho*σ*σFX;
  const sq=Math.sqrt(T),d1=(Math.log(S/K)+(r-q_adj+.5*σ*σ)*T)/(σ*sq),d2=d1-σ*sq,e=Math.exp(-r*T),eq=Math.exp(-q_adj*T);
  return put?K*e*Phi(-d2)-S*eq*Phi(-d1):S*eq*Phi(d1)-K*e*Phi(d2);
}

function autocallFull(S0,barrierPct,kiPct,couponRate,nObs,T,r,q,σ,nPaths,seed=42){
  const rand=lcg(seed),dt=T/nObs,mu=(r-q-.5*σ*σ)*dt,v=σ*Math.sqrt(dt);
  const Bc=S0*barrierPct,Bki=S0*kiPct;
  let tot=0;const callCounts=new Array(nObs).fill(0);let kiCount=0,survCount=0;const payoffs=[];
  for(let p=0;p<nPaths;p++){
    let S=S0,called=false,pv=0;
    for(let i=0;i<nObs;i++){const t=(i+1)*dt;S*=Math.exp(mu+v*bm(rand(),rand()));if(S>=Bc){pv=(1+couponRate*(i+1))*Math.exp(-r*t);callCounts[i]++;called=true;payoffs.push((1+couponRate*(i+1))*100);break;}}
    if(!called){if(S>=Bki){survCount++;pv=Math.exp(-r*T);payoffs.push(100);}else{kiCount++;const pct=S/S0;pv=pct*Math.exp(-r*T);payoffs.push(+(pct*100).toFixed(1));}}
    tot+=pv;
  }
  return{price:tot/nPaths*100,callProbs:callCounts.map(c=>c/nPaths),kiProb:kiCount/nPaths,surviveProb:survCount/nPaths,payoffs};
}
function autocallMC(S0,barrierPct,kiPct,couponRate,nObs,T,r,q,σ,nPaths,seed=42){return autocallFull(S0,barrierPct,kiPct,couponRate,nObs,T,r,q,σ,nPaths,seed).price;}

// MC Paths Generator
function genMCPathsData(S0, T, r, q, σ, numPaths=12, numSteps=60, seed=42) {
  const rand = lcg(seed);
  const dt = T / numSteps;
  const mu = (r - (q||0) - 0.5 * σ * σ) * dt;
  const v = σ * Math.sqrt(dt);
  const data = Array.from({ length: numSteps + 1 }, (_, step) => ({ step }));
  const avgPath = new Array(numSteps + 1).fill(0);
  const pathKeys = Array.from({ length: numPaths }, (_, i) => `path${i + 1}`);
  for (let p = 0; p < numPaths; p++) {
    const key = `path${p + 1}`;
    let S = S0;
    data[0][key] = S; avgPath[0] += S;
    for (let step = 1; step <= numSteps; step++) {
      const z = bm(rand(), rand());
      S *= Math.exp(mu + v * z);
      data[step][key] = S; avgPath[step] += S;
    }
  }
  avgPath.forEach((sum, step) => { data[step].avg = sum / numPaths; });
  return { data, pathKeys };
}

function genMultiMCPathsData(S1, S2, T, r, q, σ1, σ2, rho, numPaths=20, numSteps=60, seed=42) {
  const rand = lcg(seed);
  const dt = T / numSteps;
  const mu1 = (r - (q||0) - 0.5 * σ1 * σ1) * dt, v1 = σ1 * Math.sqrt(dt);
  const mu2 = (r - (q||0) - 0.5 * σ2 * σ2) * dt, v2 = σ2 * Math.sqrt(dt);
  const sqRho = Math.sqrt(Math.max(1 - rho * rho, 0));
  const data = Array.from({ length: numSteps + 1 }, (_, step) => ({ step }));
  const pathKeys1 = [], pathKeys2 = [];
  for (let p = 0; p < numPaths; p++) {
    const k1 = `A${p+1}`, k2 = `B${p+1}`;
    pathKeys1.push(k1); pathKeys2.push(k2);
    let A = S1, B = S2;
    data[0][k1] = A; data[0][k2] = B;
    for (let step = 1; step <= numSteps; step++) {
      const z1 = bm(rand(), rand()), z2 = bm(rand(), rand()), z2c = rho * z1 + sqRho * z2;
      A *= Math.exp(mu1 + v1 * z1); B *= Math.exp(mu2 + v2 * z2c);
      data[step][k1] = A; data[step][k2] = B;
    }
  }
  return { data, pathKeys1, pathKeys2 };
}

// ─── UNIVERSAL GREEKS ENGINE ────────────────────────────────────────────────
function computeGreekGrid(priceFn,params,nPts=24){
  const S0r=params.S0||100,SMIN=S0r*.38,SMAX=S0r*1.92;
  const dS=S0r*.015,dsig=.003,dr=.001,dT=1/365,dS2=dS*2;
  return Array.from({length:nPts},(_,i)=>{
    const S=SMIN+(SMAX-SMIN)*i/(nPts-1);
    const nP=2000,nSt=52,Z1=genZ(nP,nSt,42+i),Z2=genZ(nP,nSt,142+i),p=params;
    const sp=Math.max(p.sigma-dsig,.005),sup=p.sigma+dsig,rp=Math.max(p.r-dr,0),rup=p.r+dr,Tp=Math.max(p.T-dT,.005);
    const v0=priceFn(S,p,Z1,Z2),vup=priceFn(S+dS,p,Z1,Z2),vdn=priceFn(S-dS,p,Z1,Z2);
    const vup2=priceFn(S+dS2,p,Z1,Z2),vdn2=priceFn(S-dS2,p,Z1,Z2);
    const vsu=priceFn(S,{...p,sigma:sup},Z1,Z2),vsd=priceFn(S,{...p,sigma:sp},Z1,Z2);
    const vru=priceFn(S,{...p,r:rup},Z1,Z2),vrd=priceFn(S,{...p,r:rp},Z1,Z2);
    const vth=priceFn(S,{...p,T:Tp},Z1,Z2);
    const vup_su=priceFn(S+dS,{...p,sigma:sup},Z1,Z2),vup_sd=priceFn(S+dS,{...p,sigma:sp},Z1,Z2);
    const vdn_su=priceFn(S-dS,{...p,sigma:sup},Z1,Z2),vdn_sd=priceFn(S-dS,{...p,sigma:sp},Z1,Z2);
    const vth_up=priceFn(S+dS,{...p,T:Tp},Z1,Z2),vth_dn=priceFn(S-dS,{...p,T:Tp},Z1,Z2);
    const delta=(vup-vdn)/(2*dS),gamma=(vup-2*v0+vdn)/(dS*dS),theta=(vth-v0)/dT;
    const vega=(vsu-vsd)/(2*dsig),rho=(vru-vrd)/(2*dr);
    const vanna=(vup_su-vup_sd-vdn_su+vdn_sd)/(4*dS*dsig);
    const vomma=(vsu-2*v0+vsd)/(dsig*dsig);
    const charm=(vth_up-vth_dn)/(2*dS*dT);
    const speed=(-8*vup+vup2+8*vdn-vdn2)/(2*dS2*dS*dS)*(dS*dS);
    const veta=(priceFn(S,{...p,T:Tp,sigma:sup},Z1,Z2)-priceFn(S,{...p,T:Tp,sigma:sp},Z1,Z2))/(2*dsig)-vega;
    return{S:+S.toFixed(1),price:+v0.toFixed(3),delta:+delta.toFixed(4),gamma:+gamma.toFixed(5),theta:+theta.toFixed(4),vega:+(vega/100).toFixed(4),rho:+(rho/100).toFixed(4),vanna:+(vanna/100).toFixed(4),vomma:+(vomma/10000).toFixed(4),charm:+charm.toFixed(5),speed:+speed.toFixed(6),veta:+(veta/100).toFixed(4)};
  });
}

// ─── DESIGN TOKENS ──────────────────────────────────────────────────────────
const C={bg:"#030712",panel:"#0c1220",border:"#1e2d45",dim:"#2d3f5a",muted:"#4a6080",text:"#d4e4f7",bright:"#f0f8ff"};

// ─── COLORED CIRCLE ICON ────────────────────────────────────────────────────
function OptDot({color, size=9}){
  return(
    <span style={{
      display:"inline-block",
      width:size,height:size,
      borderRadius:"50%",
      background:color,
      boxShadow:`0 0 6px ${color}99, 0 0 2px ${color}`,
      flexShrink:0,
      verticalAlign:"middle"
    }}/>
  );
}

// ─── BASE UI ────────────────────────────────────────────────────────────────
function Sl({label,value,min,max,step,unit,onChange,accent="#00e5ff"}){
  const [localVal, setLocalVal] = React.useState(String(value));
  React.useEffect(() => {
    if (parseFloat(value) !== parseFloat(localVal)) setLocalVal(String(value));
  }, [value]);
  const handleInputChange = (e) => {
    setLocalVal(e.target.value);
    const parsed = parseFloat(e.target.value);
    if (!isNaN(parsed)) onChange(parsed);
  };
  return(
    <div style={{marginBottom:11}}>
      <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:3}}>
        <span style={{color:C.muted,fontSize:10}}>{label}</span>
        <div style={{display:"flex", alignItems:"center"}}>
          <input type="text" value={localVal} onChange={handleInputChange}
            onBlur={() => setLocalVal(String(value))}
            style={{background:C.bg,border:`1px solid ${C.border}`,color:C.bright,fontSize:10,fontWeight:700,width:46,padding:"3px 4px",borderRadius:4,textAlign:"right",outline:`1px solid transparent`,fontFamily:"'IBM Plex Mono',monospace",marginRight:6,transition:"border 0.2s"}}
            onFocus={(e) => e.target.style.border = `1px solid ${accent}`}
            onMouseLeave={(e) => { if (document.activeElement !== e.target) e.target.style.border = `1px solid ${C.border}` }}
          />
          <span style={{color:C.bright,fontSize:10,fontWeight:700,minWidth:10}}>{unit}</span>
        </div>
      </div>
      <input type="range" min={min} max={max} step={step} value={value} onChange={e=>onChange(Number(e.target.value))} style={{width:"100%",accentColor:accent,cursor:"pointer",height:3,marginTop:2}}/>
    </div>
  );
}

function Tog({opts,val,onChange}){
  return(
    <div style={{display:"flex",background:C.bg,borderRadius:7,border:`1px solid ${C.border}`,overflow:"hidden",marginBottom:10}}>
      {opts.map(o=><button key={String(o.v)} onClick={()=>onChange(o.v)} style={{flex:1,padding:"6px 2px",border:"none",cursor:"pointer",fontFamily:"'IBM Plex Mono',monospace",fontSize:9,letterSpacing:1,textTransform:"uppercase",background:val===o.v?"#1e2d45":"transparent",color:val===o.v?C.bright:C.muted,transition:"all .15s"}}>{o.l}</button>)}
    </div>
  );
}

function Pnl({children,style={},accent}){return<div style={{background:C.panel,borderRadius:10,border:`1px solid ${accent?accent+"33":C.border}`,padding:"14px 16px",...style}}>{children}</div>;}
function Lbl({children,style={}}){return<div style={{fontSize:8,color:C.muted,letterSpacing:3,textTransform:"uppercase",marginBottom:9,...style}}>{children}</div>;}
function Kpi({label,value,color=C.text}){return<div style={{background:"#111b2b",borderRadius:8,padding:"8px 10px",border:`1px solid ${C.border}`,textAlign:"center"}}><div style={{fontSize:8,color:C.muted,letterSpacing:2,textTransform:"uppercase",marginBottom:3}}>{label}</div><div style={{fontSize:13,fontWeight:700,color,fontFamily:"'Courier New',monospace"}}>{value}</div></div>;}

// ─── CHART HELPERS ──────────────────────────────────────────────────────────
const ORDER1=[
  {key:"price",label:"Price",     desc:"Theoretical Value",  color:"#f59e0b"},
  {key:"delta",label:"Delta Δ",   desc:"∂V/∂S",              color:"#00e5ff"},
  {key:"gamma",label:"Gamma Γ",   desc:"∂²V/∂S²",            color:"#ff6b35"},
  {key:"theta",label:"Theta Θ",   desc:"∂V/∂t (Daily)",      color:"#a78bfa"},
  {key:"vega", label:"Vega ν",    desc:"∂V/∂σ (per 1%)",     color:"#34d399"},
  {key:"rho",  label:"Rho ρ",     desc:"∂V/∂r (per 1%)",     color:"#fbbf24"},
];
const ORDER2=[
  {key:"vanna",label:"Vanna",   desc:"∂Δ/∂σ",               color:"#f472b6"},
  {key:"vomma",label:"Vomma",   desc:"∂²V/∂σ² (Volga)",     color:"#4ade80"},
  {key:"charm",label:"Charm",   desc:"∂Δ/∂t",               color:"#fb923c"},
  {key:"speed",label:"Speed",   desc:"∂Γ/∂S",               color:"#c084fc"},
  {key:"veta", label:"Veta",    desc:"∂ν/∂t",               color:"#22d3ee"},
];

function GChart({d,gk,color,label,desc,refs=[],active,onToggle}){
  const dimmed=active&&active!==gk;
  return(
    <div onClick={onToggle} style={{background:C.panel,borderRadius:10,padding:"11px 10px 5px",border:`1px solid ${active===gk?color+"77":C.border}`,cursor:"pointer",opacity:dimmed?.15:1,transition:"all .2s",transform:active===gk?"scale(1.012)":"scale(1)"}}>
      <div style={{display:"flex",justifyContent:"space-between",marginBottom:5}}>
        <span style={{fontSize:12,fontWeight:700,color,letterSpacing:.5}}>{label}</span>
        <span style={{fontSize:9,color:C.muted}}>{desc}</span>
      </div>
      <ResponsiveContainer width="100%" height={250}>
        <LineChart data={d} margin={{top:2,right:4,left:0,bottom:0}}>
          <CartesianGrid stroke={C.border} strokeDasharray="3 3"/>
          <XAxis dataKey="S" type="number" domain={['dataMin','dataMax']} tick={{fill:C.muted,fontSize:8}} tickLine={false} axisLine={{stroke:C.border}}/>
          <YAxis tick={{fill:C.muted,fontSize:8}} tickLine={false} axisLine={false} width={46} tickFormatter={v=>Math.abs(v)<0.001?v.toExponential(1):Math.abs(v)<1?v.toFixed(3):v.toFixed(1)}/>
          <Tooltip contentStyle={{background:C.panel,border:`1px solid ${color}44`,borderRadius:8,fontFamily:"'IBM Plex Mono',monospace",fontSize:10}} formatter={v=>[typeof v==="number"?v.toFixed(5):v,label]} labelFormatter={l=>`S = ${Number(l).toFixed(1)}`}/>
          {refs.map(({x,rc,rl})=><ReferenceLine key={x} x={x} stroke={rc||"#ffffff22"} strokeDasharray="4 4" label={rl?{value:rl,fill:rc,fontSize:8,position:"insideTopRight"}:undefined}/>)}
          <ReferenceLine y={0} stroke="#ffffff18"/>
          <Line type="monotone" dataKey={gk} stroke={color} strokeWidth={2} dot={false} activeDot={{r:3,fill:color,stroke:C.panel,strokeWidth:2}} isAnimationActive={false}/>
        </LineChart>
      </ResponsiveContainer>
    </div>
  );
}

function GreeksGrid({data,refs=[],order="1"}){
  const [active,setActive]=React.useState(null);
  const charts=order==="1"?ORDER1:ORDER2;
  return(
    <div style={{display:"grid",gridTemplateColumns:"repeat(2, 1fr)",gap:11}}>
      {charts.map(c=><GChart key={c.key} d={data} gk={c.key} color={c.color} label={c.label} desc={c.desc} refs={refs} active={active} onToggle={()=>setActive(a=>a===c.key?null:c.key)}/>)}
    </div>
  );
}

// ─── PAYOFF HELPERS ──────────────────────────────────────────────────────────
function plinear(K,put,n=70){return Array.from({length:n},(_,i)=>{const S=35+(210-35)*i/(n-1);return{S:+S.toFixed(1),payoff:Math.max(put?K-S:S-K,0)};});}
function plinearStrategy(p,n=70){
  const minK=Math.min(...p.legs.map(l=>l.K))||p.S0,maxK=Math.max(...p.legs.map(l=>l.K))||p.S0;
  const Smin=Math.max(0,minK*0.5),Smax=maxK*1.5;
  return Array.from({length:n},(_,i)=>{
    const S=Smin+(Smax-Smin)*i/(n-1);
    const payoff=p.legs.reduce((sum,l)=>sum+l.dir*l.qty*Math.max(l.type==='put'?l.K-S:S-l.K,0),0);
    return{S:+S.toFixed(1),payoff};
  });
}

// ─── OPTION DEFINITIONS ──────────────────────────────────────────────────────
const OPTS=[
  {id:"european",name:"European",   sub:"Black-Scholes Model",          color:"#00e5ff",cat:"Vanilla",      closedForm:true,
   dp:{S0:100,K:100,T:1,r:.05,q:0,sigma:.20,put:false},
   pf:(S,p)=>bs(S,p.K,p.T,p.r,p.q||0,p.sigma,p.put),kRef:p=>p.K,payoff:p=>plinear(p.K,p.put)},

  {id:"american",name:"American",   sub:"CRR Tree (150 steps)",         color:"#60a5fa",cat:"Vanilla",
   dp:{S0:100,K:100,T:1,r:.05,q:0,sigma:.20,put:false},
   pf:(S,p)=>binomAmer(S,p.K,p.T,p.r,p.q||0,p.sigma,150,p.put),kRef:p=>p.K,payoff:p=>plinear(p.K,p.put)},

  {id:"bermudan",name:"Bermudan",   sub:"Discrete Binomial Tree",       color:"#10b981",cat:"Vanilla",
   dp:{S0:100,K:100,T:1,r:.05,q:0,sigma:.20,put:false,nDates:4},
   pf:(S,p)=>binomBermudan(S,p.K,p.T,p.r,p.q||0,p.sigma,150,p.put,p.nDates||4),kRef:p=>p.K,payoff:p=>plinear(p.K,p.put)},

  {id:"barrier",  name:"Barrier",   sub:"Knock-Out / Knock-In",         color:"#f97316",cat:"Exotic",
   dp:{S0:100,K:100,T:1,r:.05,q:0,sigma:.20,H:80,isDown:true,isOut:true,put:false},
   pf:(S,p,Z1)=>barrierMC(S,p.K,p.T,p.r,p.q||0,p.sigma,p.H,p.isDown,p.isOut,p.put,Z1||genZ(2500,60,99)),
   kRef:p=>p.K,refs:p=>[{x:p.H,rc:p.isOut?"#f97316aa":"#22d3eeaa",rl:p.isOut?"KO":"KI"}],
   payoff:p=>Array.from({length:70},(_,i)=>{const St=30+(230-30)*i/69;const hit=p.isDown?St<=p.H:St>=p.H;return{S:+St.toFixed(1),payoff:(p.isOut?!hit:hit)?Math.max(p.put?p.K-St:St-p.K,0):0};})},

  {id:"parisian", name:"Parisian",  sub:"Excursion Window",             color:"#c084fc",cat:"Exotic",
   dp:{S0:100,K:100,T:1,r:.05,q:0,sigma:.20,H:80,isDown:true,isOut:true,window:10,put:false},
   pf:(S,p,Z1)=>parisianMC(S,p.K,p.T,p.r,p.q||0,p.sigma,p.H,p.isDown,p.isOut,p.window||10,p.put,Z1||genZ(2500,60,99)),
   kRef:p=>p.K,refs:p=>[{x:p.H,rc:p.isOut?"#c084fcaa":"#22d3eeaa",rl:p.isOut?"KO":"KI"}],
   payoff:p=>Array.from({length:70},(_,i)=>{const St=30+(230-30)*i/69;const hit=p.isDown?St<=p.H:St>=p.H;return{S:+St.toFixed(1),payoff:(p.isOut?!hit:hit)?Math.max(p.put?p.K-St:St-p.K,0):0};})},

  {id:"digital",  name:"Digital",   sub:"Cash / Asset-or-Nothing",      color:"#e879f9",cat:"Exotic",     closedForm:true,
   dp:{S0:100,K:100,T:1,r:.05,q:0,sigma:.20,isCall:true,isCash:true},
   pf:(S,p)=>digital(S,p.K,p.T,p.r,p.q||0,p.sigma,p.isCall,p.isCash),kRef:p=>p.K,
   payoff:p=>Array.from({length:60},(_,i)=>{const S=35+(210-35)*i/59;const c=p.isCall;return{S:+S.toFixed(1),payoff:c?(S>p.K?(p.isCash?1:S):0):(S<p.K?(p.isCash?1:S):0)};})},

  {id:"lookback", name:"Lookback",  sub:"Floating/Fixed Strike",        color:"#fb7185",cat:"Exotic",
   dp:{S0:100,K:100,T:1,r:.05,q:0,sigma:.20,isFloat:true,put:false},
   pf:(S,p,Z1)=>lookbackMC(S,p.K,p.T,p.r,p.q||0,p.sigma,p.isFloat,p.put,Z1||genZ(2500,60,55)),
   kRef:p=>p.isFloat?null:p.K,
   payoff:p=>Array.from({length:50},(_,i)=>{const S=50+(190-50)*i/49;return{S:+S.toFixed(1),payoff:p.isFloat?(p.put?S*.12:S*.12):(p.put?Math.max(p.K-S*.88,0):Math.max(S*1.12-p.K,0))};})},

  {id:"shout",    name:"Shout",     sub:"Optimal Lock-in",              color:"#4ade80",cat:"Exotic",
   dp:{S0:100,K:100,T:1,r:.05,q:0,sigma:.20,put:false},
   pf:(S,p,Z1)=>shoutMC(S,p.K,p.T,p.r,p.q||0,p.sigma,p.put,Z1||genZ(2500,60,33)),kRef:p=>p.K,
   payoff:p=>Array.from({length:60},(_,i)=>{const St=35+(210-35)*i/59;const Ss=Math.max(p.S0*.95,p.K);return{S:+St.toFixed(1),payoff:Math.max(p.put?Math.max(p.K-St,0):Math.max(St-p.K,0),p.put?Math.max(p.K-Ss,0):Math.max(Ss-p.K,0))};})},

  {id:"asian",    name:"Asian",     sub:"Arithmetic Average",           color:"#a78bfa",cat:"Path-Dep",
   dp:{S0:100,K:100,T:1,r:.05,q:0,sigma:.20,put:false},
   pf:(S,p,Z1)=>asianMC(S,p.K,p.T,p.r,p.q||0,p.sigma,p.put,Z1||genZ(2500,60,11)),kRef:p=>p.K,
   payoff:p=>Array.from({length:60},(_,i)=>{const St=35+(210-35)*i/59;const avg=(p.S0+St)/2;return{S:+St.toFixed(1),payoff:p.put?Math.max(p.K-avg,0):Math.max(avg-p.K,0)};})},

  {id:"basket",   name:"Basket",    sub:"2 Correlated Assets",          color:"#fbbf24",cat:"Multi-Asset",
   dp:{S0:100,S2:100,K:100,T:1,r:.05,q:0,sigma:.20,sigma2:.25,rho:.5,w1:.5,put:false},
   pf:(S,p,Z1,Z2)=>{const Zc=corrZ(Z1||genZ(2500,60,22),Z2||genZ(2500,60,33),p.rho||.5);return basketMC(S,p.S2||100,p.K,p.T,p.r,p.q||0,p.sigma,p.sigma2||.25,p.rho||.5,p.w1||.5,p.put,Z1||genZ(2500,60,22),Zc);},
   kRef:p=>p.K,payoff:p=>Array.from({length:60},(_,i)=>{const S1=35+(210-35)*i/59;const bsk=(p.w1||.5)*S1+(1-(p.w1||.5))*(p.S2||100);return{S:+S1.toFixed(1),payoff:p.put?Math.max(p.K-bsk,0):Math.max(bsk-p.K,0)};})},

  {id:"rainbow",  name:"Rainbow",   sub:"Best-of / Worst-of",           color:"#f43f5e",cat:"Multi-Asset",
   dp:{S0:100,S2:100,K:100,T:1,r:.05,q:0,sigma:.20,sigma2:.25,rho:.5,type:"best-call"},
   pf:(S,p,Z1,Z2)=>{const Zc=corrZ(Z1||genZ(2500,60,22),Z2||genZ(2500,60,33),p.rho||.5);return rainbowMC(S,p.S2||100,p.K,p.T,p.r,p.q||0,p.sigma,p.sigma2||.25,p.rho||.5,p.type||"best-call",Z1||genZ(2500,60,22),Zc);},
   kRef:p=>p.K,payoff:p=>Array.from({length:60},(_,i)=>{const S1=35+(210-35)*i/59;const S2=p.S2||100;const best=Math.max(S1,S2),worst=Math.min(S1,S2);const t=p.type||"best-call";return{S:+S1.toFixed(1),payoff:t==="best-call"?Math.max(best-p.K,0):t==="worst-call"?Math.max(worst-p.K,0):t==="best-put"?Math.max(p.K-best,0):Math.max(p.K-worst,0)};})},

  {id:"quanto",   name:"Quanto",    sub:"FX Hedged Option",             color:"#ec4899",cat:"Multi-Asset", closedForm:true,
   dp:{S0:100,K:100,T:1,r:.05,q:0,sigma:.20,sigma2:.15,rho:.3,put:false},
   pf:(S,p)=>quantoBS(S,p.K,p.T,p.r,p.q||0,p.sigma,p.sigma2||.15,p.rho||.3,p.put),kRef:p=>p.K,payoff:p=>plinear(p.K,p.put)},

  {id:"chooser",  name:"Chooser",   sub:"Call/Put Choice at t₀",        color:"#06b6d4",cat:"Other",
   dp:{S0:100,K:100,T:1,t0:.5,r:.05,q:0,sigma:.20},
   pf:(S,p,Z1)=>chooserMC(S,p.K,p.T,p.t0||.5,p.r,p.q||0,p.sigma,Z1||genZ(2500,60,77)),kRef:p=>p.K,
   payoff:p=>Array.from({length:60},(_,i)=>{const S=35+(210-35)*i/59;const Tr=p.T-(p.t0||.5);return{S:+S.toFixed(1),payoff:Math.max(bs(S,p.K,Tr,p.r,p.q||0,p.sigma,false),bs(S,p.K,Tr,p.r,p.q||0,p.sigma,true))};})},

  {id:"cliquet",  name:"Cliquet",   sub:"Periodic Returns Cap/Floor",   color:"#84cc16",cat:"Other",
   dp:{S0:100,T:2,r:.05,q:0,sigma:.20,cap:.10,floor:-.05,nPeriods:4},
   pf:(S,p,Z1)=>cliquetMC(S,p.T,p.r,p.q||0,p.sigma,p.cap||.1,p.floor||-.05,p.nPeriods||4,Z1||genZ(2500,60,55)),
   kRef:p=>null,payoff:p=>Array.from({length:60},(_,i)=>{const ret=(35+(210-35)*i/59-100)/100;const pa=Math.min(Math.max(ret,p.floor||-.05),p.cap||.1);return{S:+(35+(210-35)*i/59).toFixed(1),payoff:Math.max(pa*(p.nPeriods||4),0)*100};})},

  {id:"power",    name:"Power",     sub:"Payoff = S^n − K",             color:"#f59e0b",cat:"Other",
   dp:{S0:100,K:10000,T:1,r:.05,q:0,sigma:.20,n:2,put:false},
   pf:(S,p,Z1)=>powerMC(S,p.K,p.T,p.r,p.q||0,p.sigma,p.n||2,p.put,Z1||genZ(2500,60,88)),
   kRef:p=>null,payoff:p=>Array.from({length:60},(_,i)=>{const S=40+(200-40)*i/59;return{S:+S.toFixed(1),payoff:p.put?Math.max(p.K-Math.pow(S,p.n||2),0):Math.max(Math.pow(S,p.n||2)-p.K,0)};})},

  {id:"exchange", name:"Exchange",  sub:"max(S₂−S₁, 0) Margrabe",      color:"#38bdf8",cat:"Other",       closedForm:true,
   dp:{S0:100,S2:110,T:1,r:.05,q:0,sigma:.20,sigma2:.25,rho:.3},
   pf:(S,p)=>margrabeP(S,p.S2||110,p.T,p.r,p.sigma,p.sigma2||.25,p.rho||.3),
   kRef:p=>p.S2,payoff:p=>Array.from({length:60},(_,i)=>{const S1=35+(210-35)*i/59;return{S:+S1.toFixed(1),payoff:Math.max((p.S2||110)-S1,0)};})},

  {id:"fwdstart", name:"Fwd Start", sub:"Deferred Strike α·S(t₀)",      color:"#34d399",cat:"Other",       closedForm:true,
   dp:{S0:100,alpha:1.0,T:2,t0:.5,r:.05,q:0,sigma:.20,put:false},
   pf:(S,p)=>fwdStart(S,p.alpha||1,p.T,p.t0||.5,p.r,p.q||0,p.sigma,p.put),
   kRef:p=>null,payoff:p=>Array.from({length:60},(_,i)=>{const S=40+(200-40)*i/59;return{S:+S.toFixed(1),payoff:bs(1,p.alpha||1,p.T-(p.t0||.5),p.r,p.q||0,p.sigma,p.put)*S};})},

  {id:"autocall", name:"Autocall",  sub:"Structured Product MC",        color:"#fb923c",cat:"Structured",
   dp:{S0:100,barrierPct:1,kiPct:.6,couponRate:.10,nObs:4,T:4,r:.03,q:0,sigma:.20},
   pf:(S,p)=>autocallMC(S,p.barrierPct,p.kiPct,p.couponRate,p.nObs,p.T,p.r,p.q||0,p.sigma,2000),
   kRef:p=>null,refs:p=>[{x:p.S0*p.barrierPct,rc:"#fb923c88",rl:"AC"},{x:p.S0*p.kiPct,rc:"#ef444488",rl:"KI"}],
   payoff:p=>Array.from({length:60},(_,i)=>{const St=35+(230-35)*i/59;return{S:+St.toFixed(1),payoff:(St>=p.S0*p.barrierPct)?(1+p.couponRate*p.nObs)*100:(St<p.S0*p.kiPct)?St/p.S0*100:100};})},

  {id:"strategy", name:"Builder",   sub:"Options Portfolio",            color:"#fb7185",cat:"Strategies",   closedForm:true,
   dp:{S0:100,T:1,r:.05,q:0,legs:[{id:1,type:'call',dir:1,K:100,sigma:.20,qty:1}]},
   pf:(S,p)=>p.legs.reduce((tot,l)=>tot+l.dir*l.qty*bs(S,l.K,p.T,p.r,p.q||0,l.sigma,l.type==='put'),0),
   kRef:p=>null,refs:p=>p.legs.map(l=>({x:l.K,rc:l.type==='call'?'#00e5ff33':'#f472b633'})),payoff:p=>plinearStrategy(p)},

  {id:"volsurface",name:"3D Surface",sub:"Implied Volatility",          color:"#e879f9",cat:"Market",       isTool:true},
];

// ─── PARAM SLIDERS ──────────────────────────────────────────────────────────
function ParamSliders({opt,p,sp}){
  const id=opt.id,color=opt.color;
  if(id==="strategy"){
    return(
      <div>
        <Sl label="Spot S₀" value={p.S0} min={50} max={200} step={1} unit="" accent={color} onChange={v=>sp("S0",v)}/>
        <Sl label="Maturity T" value={p.T} min={.1} max={3} step={.1} unit=" y" accent={color} onChange={v=>sp("T",v)}/>
        <Sl label="Rate r" value={(p.r*100).toFixed(1)} min={0} max={15} step={.1} unit="%" accent={color} onChange={v=>sp("r",v/100)}/>
        <Sl label="Yield q" value={((p.q||0)*100).toFixed(1)} min={0} max={15} step={.1} unit="%" accent="#10b981" onChange={v=>sp("q",v/100)}/>
        <div style={{marginTop:18,marginBottom:8,fontSize:9,color:C.text,fontWeight:700,letterSpacing:2}}>PORTFOLIO LEGS</div>
        {p.legs.map((leg,i)=>(
          <div key={leg.id} style={{background:"#111b2b",padding:"10px",borderRadius:8,marginBottom:10,border:`1px solid ${C.border}`}}>
            <div style={{display:"flex",justifyContent:"space-between",marginBottom:8}}>
              <span style={{fontSize:10,fontWeight:"bold",color:leg.type==='call'?"#00e5ff":"#f472b6"}}>Leg {i+1}</span>
              <button onClick={()=>sp("legs",p.legs.filter(l=>l.id!==leg.id))} style={{background:"transparent",border:"none",color:"#ef4444",cursor:"pointer",fontSize:10}}>✕ Remove</button>
            </div>
            <Tog opts={[{v:1,l:"Long"},{v:-1,l:"Short"}]} val={leg.dir} onChange={v=>sp("legs",p.legs.map(l=>l.id===leg.id?{...l,dir:v}:l))}/>
            <Tog opts={[{v:'call',l:"Call"},{v:'put',l:"Put"}]} val={leg.type} onChange={v=>sp("legs",p.legs.map(l=>l.id===leg.id?{...l,type:v}:l))}/>
            <Sl label="Strike K" value={leg.K} min={50} max={200} step={1} unit="" accent={leg.type==='call'?"#00e5ff":"#f472b6"} onChange={v=>sp("legs",p.legs.map(l=>l.id===leg.id?{...l,K:v}:l))}/>
            <Sl label="Vol σ" value={(leg.sigma*100).toFixed(0)} min={5} max={80} step={1} unit="%" accent={leg.type==='call'?"#00e5ff":"#f472b6"} onChange={v=>sp("legs",p.legs.map(l=>l.id===leg.id?{...l,sigma:v/100}:l))}/>
            <Sl label="Quantity" value={leg.qty} min={1} max={10} step={1} unit="" accent="#fbbf24" onChange={v=>sp("legs",p.legs.map(l=>l.id===leg.id?{...l,qty:v}:l))}/>
          </div>
        ))}
        <button onClick={()=>sp("legs",[...p.legs,{id:Date.now(),type:'call',dir:1,K:p.S0,sigma:.20,qty:1}])} style={{width:"100%",padding:"8px 0",background:color+"11",border:`1px dashed ${color}`,color:color,borderRadius:7,cursor:"pointer",fontSize:10,fontFamily:"'IBM Plex Mono',monospace"}}>+ ADD LEG</button>
      </div>
    );
  }
  const hasS0=p.S0!==undefined&&id!=="autocall";
  const hasK=p.K!==undefined&&["european","american","bermudan","barrier","parisian","digital","lookback","shout","asian","basket","rainbow","chooser","exchange","fwdstart","quanto"].includes(id);
  const hasPut=p.put!==undefined;
  return(
    <div>
      {hasS0&&<Sl label="Spot S₀" value={p.S0} min={50} max={200} step={1} unit="" accent={color} onChange={v=>sp("S0",v)}/>}
      {id==="autocall"&&<>
        <Sl label="Spot S₀" value={p.S0} min={80} max={130} step={1} unit="" accent={color} onChange={v=>sp("S0",v)}/>
        <Sl label="Barrier AC" value={(p.barrierPct*100).toFixed(0)} min={80} max={120} step={1} unit="%" accent={color} onChange={v=>sp("barrierPct",v/100)}/>
        <Sl label="Knock-In" value={(p.kiPct*100).toFixed(0)} min={40} max={90} step={1} unit="%" accent="#ef4444" onChange={v=>sp("kiPct",v/100)}/>
        <Sl label="Coupon/obs" value={(p.couponRate*100).toFixed(1)} min={1} max={25} step={.5} unit="%" accent="#34d399" onChange={v=>sp("couponRate",v/100)}/>
        <Sl label="Observations" value={p.nObs} min={1} max={8} step={1} unit="" accent={color} onChange={v=>sp("nObs",v)}/>
      </>}
      {hasK&&<Sl label="Strike K" value={p.K} min={50} max={200} step={1} unit="" accent={color} onChange={v=>sp("K",v)}/>}
      {(id==="barrier"||id==="parisian")&&<Sl label="Barrier H" value={p.H} min={30} max={180} step={1} unit="" accent="#ef4444" onChange={v=>sp("H",v)}/>}
      {id==="parisian"&&<Sl label="Window" value={p.window||10} min={1} max={30} step={1} unit=" d" accent={color} onChange={v=>sp("window",v)}/>}
      {id==="bermudan"&&<Sl label="Exer. Dates" value={p.nDates||4} min={2} max={24} step={1} unit="" accent={color} onChange={v=>sp("nDates",v)}/>}
      {id==="power"&&<><Sl label="Strike K" value={p.K} min={1000} max={50000} step={500} unit="" accent={color} onChange={v=>sp("K",v)}/><Sl label="Power n" value={p.n||2} min={1} max={4} step={.5} unit="" accent={color} onChange={v=>sp("n",v)}/></>}
      {id==="chooser"&&<Sl label="Choice at t₀" value={(p.t0||.5).toFixed(1)} min={.1} max={p.T-.1} step={.1} unit=" y" accent="#fb923c" onChange={v=>sp("t0",v)}/>}
      {id==="fwdstart"&&<><Sl label="Moneyness α" value={((p.alpha||1)*100).toFixed(0)} min={70} max={130} step={1} unit="%" accent="#fb923c" onChange={v=>sp("alpha",v/100)}/><Sl label="Start t₀" value={(p.t0||.5).toFixed(1)} min={.1} max={p.T-.1} step={.1} unit=" y" accent="#fb923c" onChange={v=>sp("t0",v)}/></>}
      {id==="cliquet"&&<><Sl label="Cap" value={((p.cap||.1)*100).toFixed(0)} min={1} max={40} step={1} unit="%" accent={color} onChange={v=>sp("cap",v/100)}/><Sl label="Floor" value={((p.floor||-.05)*100).toFixed(0)} min={-30} max={0} step={1} unit="%" accent="#ef4444" onChange={v=>sp("floor",v/100)}/><Sl label="Periods" value={p.nPeriods||4} min={1} max={8} step={1} unit="" accent={color} onChange={v=>sp("nPeriods",v)}/></>}
      {["basket","rainbow"].includes(id)&&<><Sl label="Spot S₂" value={p.S2||100} min={50} max={200} step={1} unit="" accent="#a78bfa" onChange={v=>sp("S2",v)}/><Sl label="Vol σ₂" value={((p.sigma2||.25)*100).toFixed(0)} min={5} max={80} step={1} unit="%" accent="#a78bfa" onChange={v=>sp("sigma2",v/100)}/></>}
      {id==="exchange"&&<><Sl label="Spot S₂" value={p.S2||110} min={50} max={200} step={1} unit="" accent="#a78bfa" onChange={v=>sp("S2",v)}/><Sl label="Vol σ₂" value={((p.sigma2||.25)*100).toFixed(0)} min={5} max={80} step={1} unit="%" accent="#a78bfa" onChange={v=>sp("sigma2",v/100)}/></>}
      {id==="quanto"&&<><Sl label="FX Vol σ₂" value={((p.sigma2||.15)*100).toFixed(0)} min={5} max={80} step={1} unit="%" accent="#ec4899" onChange={v=>sp("sigma2",v/100)}/><Sl label="Correl ρ" value={((p.rho||.3)*100).toFixed(0)} min={-99} max={99} step={1} unit="%" accent="#fbbf24" onChange={v=>sp("rho",v/100)}/></>}
      {["basket","rainbow","exchange"].includes(id)&&<Sl label="Correl ρ" value={((p.rho||.5)*100).toFixed(0)} min={-99} max={99} step={1} unit="%" accent="#fbbf24" onChange={v=>sp("rho",v/100)}/>}
      {id==="basket"&&<Sl label="Weight w₁" value={((p.w1||.5)*100).toFixed(0)} min={1} max={99} step={1} unit="%" accent={color} onChange={v=>sp("w1",v/100)}/>}
      {id!=="autocall"&&<>
        <Sl label="Maturity T" value={p.T} min={.1} max={id==="fwdstart"?5:3} step={.1} unit=" y" accent={color} onChange={v=>sp("T",v)}/>
        <Sl label="Rate r" value={(p.r*100).toFixed(1)} min={0} max={15} step={.1} unit="%" accent={color} onChange={v=>sp("r",v/100)}/>
        <Sl label="Yield q" value={((p.q||0)*100).toFixed(1)} min={0} max={15} step={.1} unit="%" accent="#10b981" onChange={v=>sp("q",v/100)}/>
        <Sl label="Vol σ" value={(p.sigma*100).toFixed(0)} min={5} max={80} step={1} unit="%" accent={color} onChange={v=>sp("sigma",v/100)}/>
      </>}
      {id==="autocall"&&<>
        <Sl label="Maturity T" value={p.T} min={1} max={8} step={.5} unit=" y" accent={color} onChange={v=>sp("T",v)}/>
        <Sl label="Rate r" value={(p.r*100).toFixed(1)} min={0} max={10} step={.1} unit="%" accent="#a78bfa" onChange={v=>sp("r",v/100)}/>
        <Sl label="Yield q" value={((p.q||0)*100).toFixed(1)} min={0} max={10} step={.1} unit="%" accent="#10b981" onChange={v=>sp("q",v/100)}/>
        <Sl label="Vol σ" value={(p.sigma*100).toFixed(0)} min={5} max={60} step={1} unit="%" accent="#a78bfa" onChange={v=>sp("sigma",v/100)}/>
      </>}
      {(id==="barrier"||id==="parisian")&&<><Tog opts={[{v:true,l:"Down"},{v:false,l:"Up"}]} val={p.isDown} onChange={v=>sp("isDown",v)}/><Tog opts={[{v:true,l:"Out (KO)"},{v:false,l:"In (KI)"}]} val={p.isOut} onChange={v=>sp("isOut",v)}/></>}
      {id==="digital"&&<><Tog opts={[{v:true,l:"Call"},{v:false,l:"Put"}]} val={p.isCall} onChange={v=>sp("isCall",v)}/><Tog opts={[{v:true,l:"Cash"},{v:false,l:"Asset"}]} val={p.isCash} onChange={v=>sp("isCash",v)}/></>}
      {id==="rainbow"&&<Tog opts={[{v:"best-call",l:"Best↑"},{v:"worst-call",l:"Worst↑"},{v:"best-put",l:"Best↓"},{v:"worst-put",l:"Worst↓"}]} val={p.type||"best-call"} onChange={v=>sp("type",v)}/>}
      {id==="lookback"&&<Tog opts={[{v:true,l:"Float"},{v:false,l:"Fixed"}]} val={p.isFloat} onChange={v=>sp("isFloat",v)}/>}
      {hasPut&&id!=="digital"&&<Tog opts={[{v:false,l:"Call"},{v:true,l:"Put"}]} val={p.put} onChange={v=>sp("put",v)}/>}
    </div>
  );
}

// ─── EXTRA CHARTS ────────────────────────────────────────────────────────────
function ChartBox({title,children,accent}){
  return(
    <Pnl accent={accent} style={{marginTop:0}}>
      <Lbl>{title}</Lbl>
      {children}
    </Pnl>
  );
}

function AutocallExtraCharts({p,color}){
  const mc=React.useMemo(()=>autocallFull(p.S0,p.barrierPct,p.kiPct,p.couponRate,p.nObs,p.T,p.r,p.q||0,p.sigma,8000),[p.S0,p.barrierPct,p.kiPct,p.couponRate,p.nObs,p.T,p.r,p.q,p.sigma]);
  const callProbData=mc.callProbs.map((prob,i)=>({obs:`Obs ${i+1}\n(t=${((i+1)*p.T/p.nObs).toFixed(1)}y)`,prob:+(prob*100).toFixed(1)}));
  const histData=React.useMemo(()=>{
    const bins={};for(const v of mc.payoffs){const b=Math.floor(v/10)*10;bins[b]=(bins[b]||0)+1;}
    return Object.entries(bins).sort((a,b)=>Number(a[0])-Number(b[0])).map(([k,v])=>({range:`${k}–${Number(k)+10}`,count:v,pct:+(v/mc.payoffs.length*100).toFixed(1)}));
  },[mc.payoffs]);
  const sensData=Array.from({length:20},(_,i)=>{const σ=(10+i*3)/100;return{sigma:+(σ*100).toFixed(0),price:+autocallMC(p.S0,p.barrierPct,p.kiPct,p.couponRate,p.nObs,p.T,p.r,p.q||0,σ,2000).toFixed(2)};});
  return(
    <>
      <div style={{display:"grid",gridTemplateColumns:"repeat(3,1fr)",gap:10,padding:"8px 10px",background:"#111b2b",borderRadius:8,border:`1px solid ${C.border}`}}>
        {[{l:"P(Total Recall)",v:(mc.callProbs.reduce((a,b)=>a+b,0)*100).toFixed(1)+"%",c:color},{l:"P(Knock-In)",v:(mc.kiProb*100).toFixed(1)+"%",c:"#ef4444"},{l:"P(Capital Safe)",v:(mc.surviveProb*100).toFixed(1)+"%",c:"#34d399"}].map(k=><Kpi key={k.l} label={k.l} value={k.v} color={k.c}/>)}
      </div>
      <ChartBox title="Recall Probability per Observation Date" accent={color}>
        <ResponsiveContainer width="100%" height={250}>
          <BarChart data={callProbData} margin={{top:4,right:8,left:0,bottom:0}}>
            <CartesianGrid stroke={C.border} strokeDasharray="3 3" vertical={false}/>
            <XAxis dataKey="obs" tick={{fill:C.muted,fontSize:8}} tickLine={false} axisLine={false}/>
            <YAxis tick={{fill:C.muted,fontSize:8}} tickLine={false} axisLine={false} width={34} tickFormatter={v=>`${v}%`}/>
            <Tooltip cursor={{fill:"#ffffff0a"}} formatter={v=>[`${v}%`,"Probability"]} contentStyle={{background:C.panel,border:`1px solid ${color}44`,borderRadius:7,fontFamily:"'IBM Plex Mono',monospace",fontSize:10}}/>
            <Bar dataKey="prob" radius={[4,4,0,0]} fill={color} fillOpacity={.9}/>
          </BarChart>
        </ResponsiveContainer>
      </ChartBox>
      <ChartBox title="Payoff Distribution (%)" accent={color}>
        <ResponsiveContainer width="100%" height={250}>
          <BarChart data={histData} margin={{top:4,right:8,left:0,bottom:0}}>
            <CartesianGrid stroke={C.border} strokeDasharray="3 3" vertical={false}/>
            <XAxis dataKey="range" tick={{fill:C.muted,fontSize:8}} tickLine={false} axisLine={false}/>
            <YAxis tick={{fill:C.muted,fontSize:8}} tickLine={false} axisLine={false} width={34} tickFormatter={v=>`${v}%`}/>
            <Tooltip cursor={{fill:"#ffffff0a"}} formatter={v=>[`${v}%`,"Frequency"]} contentStyle={{background:C.panel,border:`1px solid ${color}44`,borderRadius:7,fontFamily:"'IBM Plex Mono',monospace",fontSize:10}}/>
            <Bar dataKey="pct" radius={[4,4,0,0]}>
              {histData.map((e,i)=>{const mid=Number(e.range.split("–")[0])+5;const c=mid<p.kiPct*100?"#ef4444":mid>100?color:"#34d399";return<Cell key={i} fill={c}/>;  })}
            </Bar>
          </BarChart>
        </ResponsiveContainer>
      </ChartBox>
      <ChartBox title="Price Sensitivity to Volatility" accent={color}>
        <ResponsiveContainer width="100%" height={250}>
          <LineChart data={sensData} margin={{top:2,right:8,left:0,bottom:0}}>
            <CartesianGrid stroke={C.border} strokeDasharray="3 3"/>
            <XAxis dataKey="sigma" type="number" domain={['dataMin','dataMax']} tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={{stroke:C.border}} unit="%"/>
            <YAxis tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={false} width={42} tickFormatter={v=>v.toFixed(1)+"%"}/>
            <Tooltip contentStyle={{background:C.panel,border:`1px solid ${color}44`,borderRadius:7,fontFamily:"'IBM Plex Mono',monospace",fontSize:10}} formatter={v=>[v.toFixed(2)+"%","Price"]}/>
            <Line type="monotone" dataKey="price" stroke={color} strokeWidth={2.5} dot={false} isAnimationActive={false}/>
          </LineChart>
        </ResponsiveContainer>
      </ChartBox>
    </>
  );
}

function AsianExtraCharts({p,color}){
  const Z=React.useMemo(()=>genZ(3000,60,99),[]);
  const compData=Array.from({length:20},(_,i)=>{const σ=(5+i*4)/100;return{sigma:+(σ*100).toFixed(0),asian:+asianMC(p.S0,p.K,p.T,p.r,p.q||0,σ,p.put,Z).toFixed(3),euro:+bs(p.S0,p.K,p.T,p.r,p.q||0,σ,p.put).toFixed(3)};});
  return(
    <ChartBox title="Asian vs European by Volatility" accent={color}>
      <ResponsiveContainer width="100%" height={250}>
        <LineChart data={compData} margin={{top:2,right:8,left:0,bottom:0}}>
          <CartesianGrid stroke={C.border} strokeDasharray="3 3"/>
          <XAxis dataKey="sigma" type="number" domain={['dataMin','dataMax']} tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={{stroke:C.border}} unit="%"/>
          <YAxis tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={false} width={40}/>
          <Tooltip contentStyle={{background:C.panel,border:`1px solid ${color}44`,borderRadius:7,fontFamily:"'IBM Plex Mono',monospace",fontSize:10}} formatter={v=>[v.toFixed(3)]}/>
          <Line type="monotone" dataKey="asian" stroke={color} strokeWidth={2} dot={false} name="Asian" isAnimationActive={false}/>
          <Line type="monotone" dataKey="euro" stroke="#94a3b8" strokeWidth={2} strokeDasharray="5 3" dot={false} name="European" isAnimationActive={false}/>
        </LineChart>
      </ResponsiveContainer>
      <div style={{fontSize:8,color:C.muted,marginTop:6}}>Asian option is always ≤ European (averaging effect)</div>
    </ChartBox>
  );
}

function BarrierExtraCharts({p,color}){
  const Z=React.useMemo(()=>genZ(4000,60,55),[]);
  const survData=Array.from({length:20},(_,i)=>{const H=p.isDown?40+i*5:110+i*5;const price=barrierMC(p.S0,p.K,p.T,p.r,p.q||0,p.sigma,H,p.isDown,true,p.put,Z);return{H:+H.toFixed(0),price:+price.toFixed(3)};});
  return(
    <ChartBox title={`KO Price by Barrier Level H (${p.isDown?"Down":"Up"})`} accent={color}>
      <ResponsiveContainer width="100%" height={250}>
        <LineChart data={survData} margin={{top:2,right:8,left:0,bottom:0}}>
          <CartesianGrid stroke={C.border} strokeDasharray="3 3"/>
          <XAxis dataKey="H" type="number" domain={['dataMin','dataMax']} tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={{stroke:C.border}}/>
          <YAxis tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={false} width={40}/>
          <Tooltip contentStyle={{background:C.panel,border:`1px solid ${color}44`,borderRadius:7,fontFamily:"'IBM Plex Mono',monospace",fontSize:10}} formatter={v=>[v.toFixed(4),"Price"]}/>
          <ReferenceLine x={p.H} stroke={color} strokeDasharray="4 4"/>
          <Line type="monotone" dataKey="price" stroke={color} strokeWidth={2.5} dot={false} isAnimationActive={false}/>
        </LineChart>
      </ResponsiveContainer>
    </ChartBox>
  );
}

function MCPathsChart({S0,T,r,q,sigma,color,title="Monte Carlo Paths Visualization"}){
  const {data,pathKeys}=React.useMemo(()=>genMCPathsData(S0,T,r,q,sigma,100,60),[S0,T,r,q,sigma]);
  return(
    <ChartBox title={title} accent={color}>
      <ResponsiveContainer width="100%" height={500}>
        <LineChart data={data} margin={{top:2,right:8,left:0,bottom:0}}>
          <CartesianGrid stroke={C.border} strokeDasharray="3 3"/>
          <XAxis dataKey="step" type="number" domain={['dataMin','dataMax']} tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={{stroke:C.border}} tickFormatter={v=>(v*T/60).toFixed(2)+"y"}/>
          <YAxis tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={false} width={40} tickFormatter={v=>v.toFixed(0)}/>
          <Tooltip cursor={{stroke:"#ffffff22",strokeWidth:1,strokeDasharray:"4 4"}}
            content={({active,payload,label})=>{
              if(active&&payload&&payload.length){const avgData=payload.find(p=>p.dataKey==='avg');if(!avgData)return null;
                return(<div style={{background:C.panel,border:`1px solid ${color}44`,padding:"8px 12px",borderRadius:7,fontFamily:"'IBM Plex Mono',monospace",fontSize:10}}><div style={{color:C.muted,marginBottom:4}}>Step {label}</div><div style={{color:"#ffffffaa",fontWeight:700}}>Average: {avgData.value.toFixed(2)}</div></div>);}
              return null;
            }}/>
          <ReferenceLine y={S0} stroke="#ffffff33" strokeDasharray="4 4" isFront={true}/>
          {pathKeys.map(key=><Line key={key} type="monotone" dataKey={key} stroke={color} strokeWidth={0.8} strokeOpacity={0.4} dot={false} activeDot={false} isAnimationActive={false}/>)}
          <Line type="monotone" dataKey="avg" stroke="#ffffffaa" strokeWidth={2.5} dot={false} name="Average" isAnimationActive={false}/>
        </LineChart>
      </ResponsiveContainer>
      <div style={{fontSize:8,color:C.muted,marginTop:4}}>100 simulated paths. Average converges to theoretical value.</div>
    </ChartBox>
  );
}

function MultiMCPathsChart({S1,S2,T,r,q,sigma1,sigma2,rho,color1,color2="#a78bfa",title="Correlated Multi-Asset Paths"}){
  const {data,pathKeys1,pathKeys2}=React.useMemo(()=>genMultiMCPathsData(S1,S2,T,r,q,sigma1,sigma2,rho,20,60),[S1,S2,T,r,q,sigma1,sigma2,rho]);
  return(
    <ChartBox title={title} accent={color1}>
      <ResponsiveContainer width="100%" height={250}>
        <LineChart data={data} margin={{top:2,right:8,left:0,bottom:0}}>
          <CartesianGrid stroke={C.border} strokeDasharray="3 3"/>
          <XAxis dataKey="step" type="number" domain={['dataMin','dataMax']} tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={{stroke:C.border}} tickFormatter={v=>(v*T/60).toFixed(2)+"y"}/>
          <YAxis tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={false} width={40} tickFormatter={v=>v.toFixed(0)}/>
          <ReferenceLine y={S1} stroke={color1} strokeOpacity={0.4} strokeDasharray="4 4" isFront={true}/>
          <ReferenceLine y={S2} stroke={color2} strokeOpacity={0.4} strokeDasharray="4 4" isFront={true}/>
          {pathKeys1.map(key=><Line key={key} type="monotone" dataKey={key} stroke={color1} strokeWidth={1} strokeOpacity={0.6} dot={false} activeDot={false} isAnimationActive={false}/>)}
          {pathKeys2.map(key=><Line key={key} type="monotone" dataKey={key} stroke={color2} strokeWidth={1} strokeOpacity={0.6} dot={false} activeDot={false} isAnimationActive={false}/>)}
        </LineChart>
      </ResponsiveContainer>
      <div style={{fontSize:8,color:C.muted,marginTop:6,display:"flex",gap:14}}>
        <span><span style={{color:color1}}>■</span> Asset 1 (S₁)</span>
        <span><span style={{color:color2}}>■</span> Asset 2 (S₂)</span>
        <span>ρ = {(rho*100).toFixed(0)}%</span>
      </div>
    </ChartBox>
  );
}

// ─── PRICER PAGE ─────────────────────────────────────────────────────────────
function PricerPage({opt,p,sp,dir,setDir}){
  const isFast=opt.closedForm||opt.id==="american"||opt.id==="bermudan";
  const [cp,setCp]=React.useState(p);
  const [busy,setBusy]=React.useState(false);
  const run=()=>{setBusy(true);setTimeout(()=>{setCp(p);setBusy(false);},10);};
  React.useEffect(()=>{if(isFast)setCp(p);},[p,isFast]);
  React.useEffect(()=>{setCp(p);},[opt.id]);
  const Z1=React.useMemo(()=>genZ(5000,80,42),[]);
  const Z2=React.useMemo(()=>genZ(5000,80,142),[]);
  const rawPrice=opt.pf(cp.S0,cp,Z1,Z2);
  const price=dir*rawPrice;
  const color=opt.color;

  // Apply direction to payoff/price chart
  const combinedData=React.useMemo(()=>{
    const basePayoff=opt.payoff(cp);
    return basePayoff.map(d=>{
      const pr=opt.pf(d.S,cp,Z1,Z2);
      return{...d,price:+(dir*pr).toFixed(3),payoff:+(dir*d.payoff).toFixed(3)};
    });
  },[cp,opt,Z1,Z2,dir]);

  const payoffRefs=opt.refs?opt.refs(cp).map(r=>({x:r.x,rc:r.rc,rl:r.rl})):[];
  if(opt.kRef&&opt.kRef(cp))payoffRefs.unshift({x:opt.kRef(cp),rc:"#ffffff22"});

  // ── Greeks ─────────────────────────────────────────────────────────────────
  let kpis=[];
  if(opt.id==="european"||opt.id==="american"||opt.id==="strategy"){
    let g={delta:0,gamma:0,theta:0,vega:0,rho:0,vanna:0,vomma:0};
    if(opt.id==="strategy"){
      if(cp.legs&&cp.legs.length>0){
        cp.legs.forEach(l=>{
          const S=Number(cp.S0),K=Number(l.K)||100,T=Number(cp.T),r=Number(cp.r),q=Number(cp.q||0);
          const sig=Number(l.sigma);
          if(!sig||sig<=0||T<=0||S<=0)return;
          const isPut=l.type==='put';
          const legG=bsGreeks(S,K,T,r,q,sig,isPut);
          // Compute vega directly: S * e^{-qT} * φ(d1) * √T  (per unit vol, then /100 for per-1%)
          const sq=Math.sqrt(T),d1=(Math.log(S/K)+(r-q+0.5*sig*sig)*T)/(sig*sq);
          const directVega=S*Math.exp(-q*T)*phi(d1)*sq/100;
          const mult=(Number(l.dir)||1)*(Number(l.qty)||1);
          g.delta+=legG.delta*mult; g.gamma+=legG.gamma*mult; g.theta+=legG.theta*mult;
          g.vega+=directVega*mult;  // use direct computation for robustness
          g.rho+=legG.rho*mult; g.vanna+=legG.vanna*mult; g.vomma+=legG.vomma*mult;
        });
      }
    }else{
      g=bsGreeks(cp.S0,cp.K,cp.T,cp.r,cp.q||0,cp.sigma,cp.put);
    }
    const fmt=(v,d=4)=>{const n=v*dir;return(n==null||isNaN(n)||!isFinite(n))?"—":n.toFixed(d);};
    kpis=[
      {l:"Delta Δ",v:fmt(g.delta),c:"#00e5ff"},
      {l:"Gamma Γ",v:fmt(g.gamma,5),c:"#ff6b35"},
      {l:"Theta Θ",v:fmt(g.theta),c:"#a78bfa"},
      {l:"Vega ν",v:fmt(g.vega),c:"#34d399"},
      {l:"Rho ρ",v:fmt(g.rho),c:"#fbbf24"},
      {l:"Vanna",v:fmt(g.vanna),c:"#f472b6"},
      {l:"Vomma",v:fmt(g.vomma),c:"#4ade80"},
    ];
    if(opt.id==="american"){
      const eu=bs(cp.S0,cp.K,cp.T,cp.r,cp.q||0,cp.sigma,cp.put);
      kpis=[{l:"American",v:(dir*rawPrice).toFixed(4),c:color},{l:"European",v:(dir*eu).toFixed(4),c:C.muted},{l:"Early Exer.",v:Math.max(rawPrice-eu,0).toFixed(4),c:"#fb923c"},...kpis.slice(0,4)];
    }
  }

  const dirColor=dir===1?"#34d399":"#f87171";
  const dirBg=dir===1?"#34d39915":"#f8717115";

  return(
    <div style={{display:"flex",gap:16,flexWrap:"wrap"}}>
      <div style={{flex:"0 0 200px"}}>
        <Pnl style={{position:"sticky",top:72}} accent={color}>
          {/* ── LONG / SHORT TOGGLE ── */}
          <div style={{marginBottom:14}}>
            <Lbl style={{marginBottom:6}}>Position</Lbl>
            <div style={{display:"flex",background:C.bg,borderRadius:7,border:`1px solid ${C.border}`,overflow:"hidden"}}>
              <button onClick={()=>setDir(1)} style={{flex:1,padding:"7px 4px",border:"none",cursor:"pointer",fontFamily:"'IBM Plex Mono',monospace",fontSize:10,letterSpacing:1,textTransform:"uppercase",background:dir===1?"#34d39922":"transparent",color:dir===1?"#34d399":C.muted,borderBottom:dir===1?"2px solid #34d399":"2px solid transparent",transition:"all .15s",fontWeight:dir===1?700:400}}>▲ Long</button>
              <button onClick={()=>setDir(-1)} style={{flex:1,padding:"7px 4px",border:"none",cursor:"pointer",fontFamily:"'IBM Plex Mono',monospace",fontSize:10,letterSpacing:1,textTransform:"uppercase",background:dir===-1?"#f8717122":"transparent",color:dir===-1?"#f87171":C.muted,borderBottom:dir===-1?"2px solid #f87171":"2px solid transparent",transition:"all .15s",fontWeight:dir===-1?700:400}}>▼ Short</button>
            </div>
          </div>
          <Lbl>Parameters</Lbl>
          <ParamSliders opt={opt} p={p} sp={sp}/>
          {!isFast&&(
            <div style={{borderTop:`1px solid ${C.border}`,paddingTop:12,marginTop:4}}>
              <button onClick={run} disabled={busy} style={{width:"100%",padding:"9px 0",background:"transparent",border:`1px solid ${busy?"#f59e0b":color}`,color:busy?"#f59e0b":color,borderRadius:7,cursor:busy?"not-allowed":"pointer",fontFamily:"'IBM Plex Mono',monospace",fontSize:10,letterSpacing:2,textTransform:"uppercase",transition:"all .2s"}}>
                {busy?"⏳ Computing...":"▶ Recalculate"}
              </button>
            </div>
          )}
        </Pnl>
      </div>

      <div style={{flex:1,minWidth:260,display:"flex",flexDirection:"column",gap:12,opacity:busy?0.4:1,transition:"opacity 0.2s"}}>
        {/* ── PRICE ── use option color, show Long/Short badge */}
        <Pnl accent={color}>
          <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:6}}>
            <Lbl style={{marginBottom:0}}>Theoretical Value</Lbl>
            <span style={{fontSize:8,padding:"2px 8px",borderRadius:4,background:dirBg,color:dirColor,border:`1px solid ${dirColor}44`,letterSpacing:2,fontWeight:700}}>
              {dir===1?"▲ LONG":"▼ SHORT"}
            </span>
          </div>
          <div style={{display:"flex",alignItems:"baseline",gap:10}}>
            <div style={{fontSize:46,fontWeight:700,color,fontFamily:"'Courier New',monospace",lineHeight:1,letterSpacing:1}}>
              {dir===-1&&rawPrice>0&&<span style={{color:"#f87171"}}>−</span>}{rawPrice!=null?rawPrice.toFixed(3):"-"}
            </div>
            {opt.id==="autocall"&&<span style={{fontSize:16,color:C.muted}}>% of Notional</span>}
          </div>
          {dir===-1&&<div style={{fontSize:9,color:"#f87171",marginTop:4,opacity:.8}}>Premium received (short)</div>}
        </Pnl>

        {/* ── GREEKS — original auto-fill rectangles ── */}
        {kpis.length>0&&(
          <div style={{display:"grid",gridTemplateColumns:"repeat(auto-fill,minmax(90px,1fr))",gap:8}}>
            {kpis.map(k=><Kpi key={k.l} label={k.l} value={k.v} color={k.c}/>)}
          </div>
        )}

        <Pnl accent={color}>
          <Lbl>Price (t=0) vs Payoff (T) — {dir===1?"Long":"Short"}</Lbl>
          <ResponsiveContainer width="100%" height={320}>
            <LineChart data={combinedData} margin={{top:2,right:8,left:0,bottom:0}}>
              <CartesianGrid stroke={C.border} strokeDasharray="3 3"/>
              <XAxis dataKey="S" type="number" domain={['dataMin','dataMax']} tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={{stroke:C.border}}/>
              <YAxis tick={{fill:C.muted,fontSize:9}} tickLine={false} axisLine={false} width={44} tickFormatter={v=>v.toFixed(1)}/>
              <Tooltip contentStyle={{background:C.panel,border:`1px solid ${color}44`,borderRadius:7,fontFamily:"'IBM Plex Mono',monospace",fontSize:10}} formatter={(v,name)=>[v.toFixed(3),name==="price"?"Current Price (t=0)":"Payoff at Expiry"]} labelFormatter={l=>`S = ${Number(l).toFixed(1)}`}/>
              {payoffRefs.map(({x,rc,rl})=><ReferenceLine key={x} x={x} stroke={rc||"#ffffff22"} strokeDasharray="4 4" label={rl?{value:rl,fill:rc,fontSize:8}:undefined}/>)}
              <ReferenceLine y={0} stroke="#ffffff55" strokeWidth={1.5}/>
              <ReferenceLine x={cp.S0} stroke="#ffffff44" strokeDasharray="4 4" label={{value:"Spot",fill:C.muted,fontSize:8,position:"insideTopLeft"}}/>
              <Line type="monotone" dataKey="payoff" stroke={dir===1?"#64748b":"#f87171"} strokeWidth={2} strokeDasharray="4 4" dot={false} isAnimationActive={false}/>
              <Line type="monotone" dataKey="price" stroke={color} strokeWidth={2.5} dot={false} activeDot={{r:4,fill:color,stroke:C.panel,strokeWidth:2}} isAnimationActive={false}/>
            </LineChart>
          </ResponsiveContainer>
          <div style={{display:"flex",gap:16,marginTop:12,fontSize:9,color:C.muted,justifyContent:"center",letterSpacing:1}}>
            <span><span style={{color:dir===1?"#64748b":"#f87171",fontWeight:700}}>---</span> PAYOFF AT EXPIRY</span>
            <span><span style={{color,fontWeight:700}}>—</span> CURRENT PRICE (t=0)</span>
          </div>
        </Pnl>

        {["autocall","barrier","asian","parisian","lookback","shout","chooser","cliquet","power"].includes(opt.id)&&(
          <MCPathsChart S0={cp.S0} T={cp.T} r={cp.r} q={cp.q||0} sigma={cp.sigma} color={color}/>
        )}
        {["basket","rainbow"].includes(opt.id)&&(
          <MultiMCPathsChart S1={cp.S0} S2={cp.S2||100} T={cp.T} r={cp.r} q={cp.q||0} sigma1={cp.sigma} sigma2={cp.sigma2||0.25} rho={cp.rho||0.5} color1={color}/>
        )}
        {opt.id==="autocall"&&<AutocallExtraCharts p={cp} color={color}/>}
        {opt.id==="asian"&&<AsianExtraCharts p={cp} color={color}/>}
        {opt.id==="barrier"&&<BarrierExtraCharts p={cp} color={color}/>}
      </div>
    </div>
  );
}

// ─── GREEKS PAGE ─────────────────────────────────────────────────────────────
function GreeksPage({opt,p,sp,dir,setDir}){
  const isFast=opt.closedForm||opt.id==="american"||opt.id==="bermudan";
  const [data,setData]=React.useState(null);
  const [busy,setBusy]=React.useState(false);
  const [order,setOrder]=React.useState("1");
  const refs=(opt.refs?opt.refs(p):[]).map(r=>({x:r.x,rc:r.rc,rl:r.rl}));
  const K=opt.kRef?opt.kRef(p):null;
  if(K)refs.push({x:K,rc:"#ffffff22"});
  const run=React.useCallback(()=>{setBusy(true);setTimeout(()=>{setData(computeGreekGrid(opt.pf,p));setBusy(false);},10);},[opt,p]);
  React.useEffect(()=>{if(isFast){const t=setTimeout(run,10);return()=>clearTimeout(t);}},[p,isFast,run]);
  React.useEffect(()=>{run();},[opt.id]);

  // Apply direction to greeks data
  const dirData=React.useMemo(()=>{
    if(!data)return null;
    if(dir===1)return data;
    return data.map(row=>{
      const r={...row};
      ["price","delta","gamma","theta","vega","rho","vanna","vomma","charm","speed","veta"].forEach(k=>{if(r[k]!==undefined)r[k]=+(r[k]*dir).toFixed(6);});
      return r;
    });
  },[data,dir]);

  return(
    <div style={{display:"flex",gap:16,flexWrap:"wrap"}}>
      <div style={{flex:"0 0 200px"}}>
        <Pnl style={{position:"sticky",top:72}} accent={opt.color}>
          {/* ── LONG / SHORT TOGGLE ── */}
          <div style={{marginBottom:14}}>
            <Lbl style={{marginBottom:6}}>Position</Lbl>
            <div style={{display:"flex",background:C.bg,borderRadius:7,border:`1px solid ${C.border}`,overflow:"hidden"}}>
              <button onClick={()=>setDir(1)} style={{flex:1,padding:"7px 4px",border:"none",cursor:"pointer",fontFamily:"'IBM Plex Mono',monospace",fontSize:10,letterSpacing:1,textTransform:"uppercase",background:dir===1?"#34d39922":"transparent",color:dir===1?"#34d399":C.muted,borderBottom:dir===1?"2px solid #34d399":"2px solid transparent",transition:"all .15s",fontWeight:dir===1?700:400}}>▲ Long</button>
              <button onClick={()=>setDir(-1)} style={{flex:1,padding:"7px 4px",border:"none",cursor:"pointer",fontFamily:"'IBM Plex Mono',monospace",fontSize:10,letterSpacing:1,textTransform:"uppercase",background:dir===-1?"#f8717122":"transparent",color:dir===-1?"#f87171":C.muted,borderBottom:dir===-1?"2px solid #f87171":"2px solid transparent",transition:"all .15s",fontWeight:dir===-1?700:400}}>▼ Short</button>
            </div>
          </div>
          <Lbl>Parameters</Lbl>
          <ParamSliders opt={opt} p={p} sp={sp}/>
          <div style={{borderTop:`1px solid ${C.border}`,paddingTop:12,marginTop:4}}>
            <div style={{width:"100%",marginBottom:10}}>
              <Tog opts={[{v:"1",l:"1st Order"},{v:"2",l:"2nd Order"}]} val={order} onChange={setOrder}/>
            </div>
            {isFast?(
              <div style={{width:"100%",padding:"9px 0",background:"transparent",border:`1px solid ${opt.color}`,color:opt.color,borderRadius:7,fontFamily:"'IBM Plex Mono',monospace",fontSize:10,letterSpacing:2,textTransform:"uppercase",textAlign:"center"}}>⚡ Real-Time</div>
            ):(
              <button onClick={run} disabled={busy} style={{width:"100%",padding:"9px 0",background:"transparent",border:`1px solid ${busy?"#f59e0b":opt.color}`,color:busy?"#f59e0b":opt.color,borderRadius:7,cursor:busy?"not-allowed":"pointer",fontFamily:"'IBM Plex Mono',monospace",fontSize:10,letterSpacing:2,textTransform:"uppercase",transition:"all .2s"}}>
                {busy?"⏳ Computing...":"▶ Recalculate"}
              </button>
            )}
            <div style={{marginTop:8,fontSize:8,color:C.muted,textAlign:"center",lineHeight:1.5}}>24 pts · {isFast?"Closed-Form":"2,000 MC Paths"}<br/>Central Finite Differences</div>
          </div>
        </Pnl>
      </div>
      <div style={{flex:1,minWidth:0}}>
        <div style={{opacity:busy&&!isFast?0.4:1,transition:"opacity 0.2s"}}>
          {dirData&&(
            <>
              <GreeksGrid data={dirData} refs={refs} order={order}/>
              {order==="2"&&(
                <div style={{marginTop:14,padding:"11px 16px",background:C.panel,borderRadius:8,border:`1px solid ${C.border}`,fontSize:9,color:C.muted,display:"flex",gap:18,flexWrap:"wrap"}}>
                  {[{n:"Vanna",f:"∂Δ/∂σ",c:"#f472b6"},{n:"Vomma",f:"∂²V/∂σ² (Volga)",c:"#4ade80"},{n:"Charm",f:"∂Δ/∂t",c:"#fb923c"},{n:"Speed",f:"∂Γ/∂S",c:"#c084fc"},{n:"Veta",f:"∂ν/∂t",c:"#22d3ee"}].map(({n,f,c})=><span key={n}><span style={{color:c,fontWeight:700}}>{n}</span> = {f}</span>)}
                </div>
              )}
            </>
          )}
        </div>
      </div>
    </div>
  );
}

// ─── VOL SURFACE ──────────────────────────────────────────────────────────────
function generate3DVolSurface(S0,baseVol,skewFactor,smileFactor){
  const strikes=[],maturities=[],zData=[];
  for(let k=S0*.5;k<=S0*1.5;k+=S0*.05)strikes.push(k.toFixed(0));
  for(let t=0.1;t<=2.0;t+=0.1)maturities.push(t.toFixed(1));
  for(let i=0;i<maturities.length;i++){
    const T=Number(maturities[i]),zRow=[];
    for(let j=0;j<strikes.length;j++){
      const K=Number(strikes[j]),moneyness=Math.log(K/S0);
      const skew=skewFactor/Math.sqrt(T),smile=smileFactor/Math.sqrt(T);
      zRow.push(Math.max(0.01,baseVol+(skew*moneyness)+(smile*moneyness*moneyness))*100);
    }
    zData.push(zRow);
  }
  return{strikes,maturities,zData};
}

function VolSurfacePage({color}){
  const [S0,setS0]=React.useState(100);
  const [baseVol,setBaseVol]=React.useState(0.20);
  const [skewFactor,setSkewFactor]=React.useState(-0.15);
  const [smileFactor,setSmileFactor]=React.useState(0.08);
  const {strikes,maturities,zData}=React.useMemo(()=>generate3DVolSurface(S0,baseVol,skewFactor,smileFactor),[S0,baseVol,skewFactor,smileFactor]);
  return(
    <div style={{display:"flex",gap:16,flexWrap:"wrap"}}>
      <div style={{flex:"0 0 200px"}}>
        <Pnl style={{position:"sticky",top:72}} accent={color}>
          <Lbl>Base Parameters</Lbl>
          <Sl label="Spot S₀" value={S0} min={50} max={200} step={1} unit="" accent={color} onChange={setS0}/>
          <Sl label="ATM Vol σ₀" value={(baseVol*100).toFixed(0)} min={5} max={80} step={1} unit="%" accent={color} onChange={v=>setBaseVol(v/100)}/>
          <div style={{marginTop:18,marginBottom:8,fontSize:9,color:C.text,fontWeight:700,letterSpacing:2}}>SMILE DYNAMICS</div>
          <Sl label="Skew (Slope)" value={skewFactor} min={-0.50} max={0.50} step={0.01} unit="" accent="#38bdf8" onChange={setSkewFactor}/>
          <Sl label="Smile (Convexity)" value={smileFactor} min={0} max={0.50} step={0.01} unit="" accent="#f472b6" onChange={setSmileFactor}/>
          <div style={{marginTop:16,fontSize:9,color:C.muted,lineHeight:1.6}}>Drag the chart to rotate the 3D surface.</div>
        </Pnl>
      </div>
      <div style={{flex:1,minWidth:0}}>
        <Pnl accent={color}>
          <Lbl>Term Structure & Volatility Skew 3D</Lbl>
          <div style={{width:'100%',height:500}}>
            <Plot data={[{z:zData,x:strikes,y:maturities,type:'surface',colorscale:[[0,'#00e5ff'],[0.5,'#a78bfa'],[1,'#f472b6']],showscale:false}]}
              layout={{autosize:true,margin:{l:0,r:0,b:10,t:10},paper_bgcolor:'transparent',plot_bgcolor:'transparent',font:{color:C.muted,family:'"IBM Plex Mono", monospace',size:10},scene:{xaxis:{title:'Strike K',gridcolor:C.border,zerolinecolor:C.border,showbackground:false},yaxis:{title:'Maturity T (Years)',gridcolor:C.border,zerolinecolor:C.border,showbackground:false},zaxis:{title:'Implied Vol (%)',gridcolor:C.border,zerolinecolor:C.border,showbackground:false},camera:{eye:{x:1.5,y:1.5,z:0.6}}}}}
              style={{width:'100%',height:'100%'}} config={{responsive:true,displayModeBar:false}}/>
          </div>
        </Pnl>
      </div>
    </div>
  );
}

// ─── OPTION PAGE ─────────────────────────────────────────────────────────────
function OptionPage({opt}){
  const [view,setView]=React.useState("pricer");
  const [params,setParams]=React.useState({...opt.dp});
  const [dir,setDir]=React.useState(1); // 1 = Long, -1 = Short (shared across pricer & greeks)
  const sp=(k,v)=>setParams(p=>({...p,[k]:v}));
  const color=opt.color;
  if(opt.isTool&&opt.id==="volsurface")return<VolSurfacePage color={color}/>;
  return(
    <div>
      <div style={{display:"flex",gap:12,alignItems:"center",marginBottom:20,flexWrap:"wrap"}}>
        <div style={{display:"flex",background:C.bg,borderRadius:8,border:`1px solid ${C.border}`,overflow:"hidden"}}>
          {[{v:"pricer",l:"💰 Pricer"},{v:"greeks",l:"Δ Greeks f(S)"}].map(o=>(
            <button key={o.v} onClick={()=>setView(o.v)} style={{padding:"9px 18px",border:"none",cursor:"pointer",fontFamily:"'IBM Plex Mono',monospace",fontSize:10,letterSpacing:2,textTransform:"uppercase",background:view===o.v?color+"22":"transparent",color:view===o.v?color:C.muted,borderBottom:view===o.v?`2px solid ${color}`:"2px solid transparent",transition:"all .2s"}}>
              {o.l}
            </button>
          ))}
        </div>
        <div style={{fontSize:10,color:C.muted}}>{opt.sub}</div>
        <span style={{fontSize:8,padding:"2px 8px",borderRadius:4,background:opt.closedForm?"#00e5ff11":"#f59e0b11",color:opt.closedForm?"#00e5ff":"#f59e0b",border:`1px solid ${opt.closedForm?"#00e5ff33":"#f59e0b33"}`,letterSpacing:2}}>
          {opt.closedForm?"CLOSED-FORM":"MONTE CARLO"}
        </span>
      </div>
      {view==="pricer"&&<PricerPage opt={opt} p={params} sp={sp} dir={dir} setDir={setDir}/>}
      {view==="greeks"&&<GreeksPage opt={opt} p={params} sp={sp} dir={dir} setDir={setDir}/>}
    </div>
  );
}

// ─── SIDEBAR ─────────────────────────────────────────────────────────────────
const CATS=["Vanilla","Exotic","Path-Dep","Multi-Asset","Other","Structured","Strategies","Market"];
function Sidebar({sel,onSel}){
  const groups=CATS.map(cat=>({cat,items:OPTS.filter(t=>t.cat===cat)})).filter(g=>g.items.length);
  return(
    <div style={{flex:"0 0 188px",background:C.panel,borderRadius:12,border:`1px solid ${C.border}`,padding:"12px 8px",alignSelf:"flex-start",position:"sticky",top:72}}>
      {groups.map(({cat,items})=>(
        <div key={cat} style={{marginBottom:14}}>
          <div style={{fontSize:8,color:C.muted,letterSpacing:3,textTransform:"uppercase",marginBottom:7,paddingLeft:8}}>{cat}</div>
          {items.map(t=>(
            <button key={t.id} onClick={()=>onSel(t.id)} style={{width:"100%",textAlign:"left",padding:"7px 8px",borderRadius:7,border:"none",background:sel===t.id?"#1a2d45":"transparent",borderLeft:sel===t.id?`2px solid ${t.color}`:"2px solid transparent",cursor:"pointer",fontFamily:"'IBM Plex Mono',monospace",marginBottom:1,transition:"all .15s"}}>
              <div style={{display:"flex",alignItems:"center",gap:8}}>
                <OptDot color={t.color} size={sel===t.id?10:8}/>
                <div>
                  <div style={{fontSize:10,fontWeight:700,color:sel===t.id?t.color:"#7a90a8"}}>{t.name}</div>
                  <div style={{fontSize:8,color:"#3d5268",marginTop:1}}>{t.sub}</div>
                </div>
              </div>
            </button>
          ))}
        </div>
      ))}
    </div>
  );
}

// ─── APP ─────────────────────────────────────────────────────────────────────
export default function App(){
  const [sel,setSel]=React.useState("european");
  const opt=OPTS.find(t=>t.id===sel);
  return(
    <div style={{minHeight:"100vh",background:C.bg,color:C.text,fontFamily:"'IBM Plex Mono',monospace",boxSizing:"border-box"}}>

      {/* HERO */}
      <div style={{background:"linear-gradient(180deg,#070f1f 0%,#030712 100%)",borderBottom:`1px solid ${C.border}`,padding:"24px 28px 0"}}>
        <div style={{maxWidth:1480,margin:"0 auto"}}>
          <div style={{textAlign:"center",paddingBottom:18}}>
            <div style={{fontSize:9,letterSpacing:8,color:C.muted,textTransform:"uppercase",marginBottom:10}}>Equity Derivatives Pricing Toolkit</div>
            <h1 style={{margin:"0 0 10px",fontFamily:"'Courier New',monospace",fontSize:"clamp(26px,4vw,44px)",fontWeight:700,letterSpacing:4,lineHeight:1,background:"linear-gradient(110deg,#d4e4f7 0%,#00e5ff 40%,#f59e0b 75%,#fb923c 100%)",WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent"}}>
              OPTIONS  LAB
            </h1>
            <div style={{fontSize:10,color:C.muted,letterSpacing:2,marginBottom:18}}>
              {OPTS.length} Option Types &nbsp;·&nbsp; 6 First-Order Greeks &nbsp;·&nbsp; 5 Second-Order Greeks &nbsp;·&nbsp; Dynamic Greeks Profiling
            </div>
            {/* Pills nav with colored dots */}
            <div style={{display:"flex",gap:6,flexWrap:"wrap",justifyContent:"center",paddingBottom:0}}>
              {OPTS.map(t=>(
                <button key={t.id} onClick={()=>setSel(t.id)} style={{padding:"6px 12px",borderRadius:"8px 8px 0 0",border:`1px solid ${sel===t.id?t.color:C.border}`,borderBottom:"none",background:sel===t.id?t.color+"22":C.panel,color:sel===t.id?t.color:C.muted,cursor:"pointer",fontSize:10,letterSpacing:.5,fontFamily:"'IBM Plex Mono',monospace",transition:"all .2s",boxShadow:sel===t.id?`0 -2px 8px ${t.color}22`:"none",display:"flex",alignItems:"center",gap:6}}>
                  <OptDot color={t.color} size={sel===t.id?9:7}/>
                  {t.name}
                </button>
              ))}
            </div>
          </div>
        </div>
      </div>

      {/* STICKY SUB-BAR */}
      <div style={{position:"sticky",top:0,zIndex:100,background:C.bg+"f4",backdropFilter:"blur(16px)",borderBottom:`1px solid ${C.border}`,padding:"9px 28px",display:"flex",alignItems:"center",gap:14}}>
        <OptDot color={opt.color} size={10}/>
        <div style={{fontSize:14,fontWeight:700,color:opt.color,fontFamily:"'Courier New',monospace",letterSpacing:1}}>{opt.name}</div>
        <div style={{fontSize:9,color:C.muted,borderLeft:`1px solid ${C.border}`,paddingLeft:14}}>{opt.sub}</div>
        <div style={{marginLeft:"auto",fontSize:9,color:C.dim,letterSpacing:2}}>BLACK-SCHOLES · MONTE CARLO · {new Date().getFullYear()}</div>
      </div>

      {/* LAYOUT */}
      <div style={{display:"flex",gap:16,padding:"18px 20px 60px",maxWidth:1480,margin:"0 auto"}}>
        <Sidebar sel={sel} onSel={setSel}/>
        <div style={{flex:1,minWidth:0}}>
          <OptionPage key={sel} opt={opt}/>
        </div>
      </div>
    </div>
  );
}
