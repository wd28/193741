numbeOfEdgeCoverings:{[x]
    if[not all any each x; :0];
    if[not all any each flip x; :0];
    if[not any raze[x]=1; :1];
    r:first where any each x=1;
    c:first where x[r]=1;
    x[r;c]:2;s:.z.s[x];
    x[r;c]:0;s+:.z.s[x];
    :s;
 };

numberOfEdgeCoveringsForSubset:{[x;y]
    r:count[x];ry:r#y;cy:r _y;
    xor:{(x and not y) or (y and not x)};
    if[xor[any ry; any cy]; :0];
    x:x where ry;
    x:x[;where cy];
    :numbeOfEdgeCoverings[x];
 };
    
subsets:{c:(count[x]+count[x[0]]);$[c=1;enlist each 01b;cross/[c#enlist 01b]]};

numberOfEdgeCoveringsForAllSubsets:{[x] subsets[x]!numberOfEdgeCoveringsForSubset[x] each subsets[x]};

blocks:([] matrix:(); nEdges:`long$(); nVertices:`long$(); alpha:`long$(); beta:`long$(); s:`long$(); coveringsForSubsets:());

addBlock:{
    nEdges:sum raze x;
    nVertices:count[x] + count[x[0]];
    coveringsForSubsets:numberOfEdgeCoveringsForAllSubsets[x];
    alpha:coveringsForSubsets[nVertices#1b];
    beta:coveringsForSubsets[0b,(nVertices-1)#1b];
    s:alpha + beta;
    `blocks upsert ([] matrix:enlist x;nEdges:nEdges;nVertices:nVertices;alpha:alpha;beta:beta;s:s;coveringsForSubsets:enlist coveringsForSubsets);
 };

addBlock[enlist enlist 1]; //edge
addBlock[(1 1; 1 1)]; //square
addBlock[(1 1 1; 1 1 1)]; //square with additional path
addBlock[flip (1 1 1; 1 1 1)]; //square with additional path - flipped
addBlock[(1 0 1; 1 1 0; 0 1 1)]; //hexagon
addBlock[(1 1 1; 1 1 0; 0 1 1)]; //hexagon with additional edge from the top
addBlock[(1 0 1; 1 1 0; 0 1 1; 0 1 1)]; //hexagon with additional 2-edge path
addBlock[(1 0 1; 1 0 1; 1 1 0; 0 1 1)]; //hexagon with additional 2-edge path
addBlock[(1 0 1 1; 1 1 0 0; 0 1 1 1)]; //hexagon with additional 2-edge path
addBlock[(1 0 0 1; 1 1 0 0; 0 1 1 0; 0 0 1 1)]; //octagon

startingSet:([] alpha:enlist 0; beta:enlist 1; s:enlist 1);

getValuesForTwo:{[x1;x2] :`alpha`beta`s!(alpha:s - beta;beta:x1[`beta]*x2[`beta];s:x1[`s]*x2[`s])};
getValuesForBlock:{[block;x]
    beta:sum{if[y[0];:0]; :z * */[?[1_y;x`s;x`alpha]]}[x]'[key block`coveringsForSubsets; value block`coveringsForSubsets];
    alpha:sum{if[not y[0];:0]; :z * */[?[1_y;x`s;x`alpha]]}[x]'[key block`coveringsForSubsets; value block`coveringsForSubsets];
    :`alpha`beta`s!(alpha;beta;alpha + beta);
 };

getPairsOfItems:{[gset;maxv] raze { (enlist each select from y where alpha <= x % z`alpha),\:(enlist z)}[maxv;gset]'[select from gset where alpha <= maxv]};
getBlockItems:{[gset;maxvp;maxvs;nItems]
    a:select from gset where alpha <= maxvs, s <= maxvp;
    if[nItems = 1; :enlist each a];
    b:.z.s[gset;;;nItems - 1]'[maxvp div a[`s]; maxvs - a[`alpha]];
    .ovs.a:(gset;maxvp;maxvs;nItems;a;b);
    :raze {x,/:y}'[enlist each a;b]
 };

getBlockValues:{[gset;maxv;block] items:getBlockItems[gset;maxv div block`s; maxv - block`alpha; block[`nVertices]-1]; :getValuesForBlock[block] each items};

.v.maxset:67;

upgradeSet:{[gset;maxv]
    newset:gset;
    newset,:./:[getValuesForTwo;getPairsOfItems[gset;maxv]];
    newset,:raze getBlockValues[gset;maxv;] each blocks;
    show `x;
    :`alpha`beta xasc select from (distinct newset) where alpha <= maxv;
 };


missing:til[68] except exec distinct alpha from upgradeSet[;67]/[startingSet];

s:upgradeSet[;1000]/[12;startingSet];
probablyMissing:til[1001] except exec distinct alpha from s;