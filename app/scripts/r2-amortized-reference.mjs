// Standalone R2 counterexample replay. No production imports.
function replay() {
  const assert=(b,msg)=>{if(!b)throw Error(msg)};
  const EXIT=-1, NONE=-2;
  const rows=[];
  let frames=0,workChecks=0,scheduleChecks=0;
  for(const geometric of [false,true]) for(let m=1;m<=12;m++){
    const n=2*m+1;
    const side=j=>m+j;
    const target=c=>c===m?EXIT:c<m?c+1:c-m;
    const axis=c=>geometric&&c>m?1:0;
    const height=c=>c<=m?m-c+1:m-(c-m)+2;
    const initial=()=>({p:[...Array.from({length:m},(_,i)=>side(i+1)),...Array.from({length:m+1},(_,i)=>i)],a:Array(n).fill(0),arrival:Array(n).fill(0),t:0});
    function step(s,open){
      const occupied=new Set(s.p.filter(c=>c>=0)),owner=new Map(),want=Array(n).fill(NONE);
      const older=(k,j)=>s.a[k]>s.a[j]||s.a[k]===s.a[j]&&k<j;
      for(let k=0;k<n;k++){
        const c=s.p[k];if(c<0)continue;
        const d=target(c);if(d!==EXIT&&!occupied.has(d)&&(!owner.has(d)||older(k,owner.get(d))))owner.set(d,k);
      }
      for(let k=0;k<n;k++){
        const c=s.p[k];if(c<0)continue;
        const d=target(c),a=d===EXIT?s.arrival[k]:axis(c);
        if(a===s.t%2&&(d===EXIT||owner.get(d)===k))want[k]=d;
      }
      const p=[...s.p],a=[...s.a],arrival=[...s.arrival];let moves=0,admissions=0;
      for(let k=0;k<n;k++)if(s.p[k]>=0){
        if(want[k]===NONE)a[k]++;
        else{p[k]=want[k];a[k]=0;arrival[k]=want[k]===EXIT?0:axis(s.p[k]);moves++;}
      }
      if(open){
        const empty=new Set(p.filter(c=>c>=0));
        for(let j=1;j<=m;j++){const c=side(j);if(occupied.has(c)||empty.has(c))continue;
          const k=p.indexOf(EXIT);if(k<0)continue;p[k]=c;a[k]=0;arrival[k]=0;empty.add(c);admissions++;}
      }
      const next={p,a,arrival,t:s.t+1};
      const cells=p.filter(c=>c>=0);assert(new Set(cells).size===cells.length,"collision");
      for(let k=0;k<n;k++)if(s.p[k]>=0&&want[k]!==NONE)assert(!cells.includes(s.p[k]),"departure not vacant");
      return {next,want,moves,admissions};
    }
    const phi=s=>s.p.reduce((v,c)=>v+(c<0?0:height(c)),0);
    const first=(geometric?3:4)*2**m+2*m-4;
    const starts=Array(m+1),periods=Array(m+1);
    starts[m]=0;periods[m]=geometric?3:4;
    if(geometric){starts[m-1]=4;periods[m-1]=6;for(let j=m-2;j>=0;j--){starts[j]=starts[j+1]+periods[j+1]+2;periods[j]=2*periods[j+1];}}
    else {const fillStart=Array(m+1),fillPeriod=Array(m+1);fillStart[m]=2;fillPeriod[m]=4;
      for(let j=m-1;j>=1;j--){fillStart[j]=fillStart[j+1]+fillPeriod[j+1]+2;fillPeriod[j]=2*fillPeriod[j+1];}
      for(let j=0;j<m;j++){starts[j]=fillStart[j+1]+fillPeriod[j+1];periods[j]=2*fillPeriod[j+1];}}
    let s=initial(),seen=Array(m+1).fill(0),firstSeen=-1;
    for(let t=0;t<=first;t++){
      const q=step(s,true);
      for(let k=0;k<n;k++)if(s.p[k]>=0&&s.p[k]<=m&&q.want[k]!==NONE){
        const c=s.p[k];assert(t===starts[c]+seen[c]++*periods[c],"trunk schedule");scheduleChecks++;}
      if(q.want[m]!==NONE&&firstSeen<0)firstSeen=t;
      s=q.next;frames++;
    }
    assert(firstSeen===first,"first movement formula");
    s=initial();const work=phi(s),deadline=2*(work-height(0)+1);
    let closedFirst=-1,quiet=0,t=0;
    while(s.p.some(c=>c>=0)){
      const q=step(s,false);
      assert(phi(q.next)+q.moves<=phi(s),"work accounting");workChecks++;
      quiet=q.moves?0:quiet+1;assert(quiet<2,"quiet block");
      if(q.want[m]!==NONE&&closedFirst<0)closedFirst=t;
      s=q.next;t++;assert(t<=2*work,"drain deadline");
    }
    assert(closedFirst>=0&&closedFirst<deadline,"closed focal deadline");
    rows.push({geometric,merges:m,roadCells:n,openFirstMove:firstSeen,closedFirstMove:closedFirst,closedWorkBound:deadline,drainSteps:t});
  }
  return {frames,workChecks,scheduleChecks,rows,scope:"Independent protected-service reference model, L=0, G=1, adversarial side admissions. Not a production simulator or Lean kernel check."};
}
console.log(JSON.stringify(replay(), null, 2));
