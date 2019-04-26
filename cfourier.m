(* ::Package:: *)

ExpandNCM::usage="Expand non-commutative-multiplication polynomial.";
sendNCM::usage="apply f to ncm monomial, and g to the coefficient.";
AppToNCM::usage="apply f to ncm polynomial, and g to the coefficient.";
takeDag::usage="Take the dagger of a ncm polynomial, d->o, o->d.";
cfourier::usage="Take the fourier transformation of the c[o/d,{i,j,...},a].";
cSum::usage="Sum over {i,j,...}.";
\[Delta]::usage="Dirac Delta function";





Clear[sendNCM,expandNCM]
(*a[__] to represent fermion/boson operator, d/o represent dagger or not*)
expandNCM[(h:NonCommutativeMultiply)[a___,b_Plus,c___]]:=Distribute[h[a,b,c],Plus,h,Plus,expandNCM[h[##]]&]
expandNCM[(h:NonCommutativeMultiply)[a___,b_Times,c___]]:=Most[b]expandNCM[h[a,Last[b],c]]
expandNCM[a_]:=ExpandAll[a]
ExpandNCM[exp_]:=Block[{exp1},
exp1=expandNCM[exp];
Distribute[fggsfsf[exp1]]/.fggsfsf->expandNCM
]
(*g acts on coefficients, f acts on NonCM*)
sendNCM[(h:Times)[a___,b_NonCommutativeMultiply],g_,f_]:=g[Times[a]]f[b]
sendNCM[b_NonCommutativeMultiply,g_,f_]:=f[b]
sendNCM[(h:Times)[a___,c[k___]],g_,f_]:=g[Times[a]]f[c[k]]
sendNCM[c[k___],g_,f_]:=f[c[k]]
sendNCM[(h:Times)[tt___,a[k___]],g_,f_]:=g[Times[tt]]f[a[k]]
sendNCM[a[k___],g_,f_]:=f[a[k]]
sendNCM[ff_Function,g_,f_]:=f[ff]
sendNCM[(h:Times)[tt___,ff_Function],g_,f_]:=g[Times[tt]]f[ff]

AppToNCM[exp_,g_,f_]:=Distribute[sendNCM[ExpandNCM[exp],g,f]]
takeDag[exp_]:=AppToNCM[exp,Conjugate,Reverse]/.{d->o,o->d}


generateKlist[n_,l_]:=Block[{kk={kx,ky,kz,kw}},Array[ToExpression[ToString[kk[[#2]]]<>ToString[#1]]&,{n,l}]]

Begin["cfourierPrivate`"];
cfourier1c[c[o,i:{__},\[Alpha]___],k:{__}]:={c[o,k,\[Alpha]],E^(I k.i)}
cfourier1c[c[d,i:{__},\[Alpha]___],k:{__}]:={c[d,k,\[Alpha]],E^(-I k.i)}
cfouriernc[bbb_,dim_]:=Block[{exp},
exp=Thread@MapThread[cfourier1c,{{bbb},generateKlist[Length@{bbb},dim]}];
Times@@Flatten[exp]
]
cfouriernc[bbb__,dim_]:=Block[{exp},
exp=Thread@MapThread[cfourier1c,{{bbb},generateKlist[Length@{bbb},dim]}];
(Times@@exp[[2]])NonCommutativeMultiply@@exp[[1]]
]
End[];

cfourier[exp_,dim_]:=Block[{exp1},
exp1=AppToNCM[exp,Identity,fsfjksahdfj[#,dim]&]/.NonCommutativeMultiply[ss__]:>ss;
exp1/.fsfjksahdfj-> cfourierPrivate`cfouriernc
]


ClearAll[exponentExpand]
exponentExpand[(h:Power)[a_,b_],i:{___}]:=Block[{ilist},
ilist=CoefficientList[b,i];
If[Length@ilist<2,"No "<>ToString[i],
If[Length@i==1,a^ilist[[1]] exp[ilist[[2]],i[[1]]],
If[Length@i==2,a^ilist[[1,1]] exp[{ilist[[2,1]],ilist[[1,2]]},i],
If[Length@i==3,a^ilist[[1,1,1]] exp[{ilist[[2,1,1]],ilist[[1,2,1]],ilist[[1,1,2]]},i]]]]
]
]
exponentExpand[(h:Times)[a___],i:{__}]:=h@@(exponentExpand[#,i]&/@{a})
exponentExpand[a_,i_]:=a

cfourierExpand[exp_,i_]:=AppToNCM[exp,exponentExpand[#,i]&,Identity]

Begin["cfourierPrivateS`"];
cSumss[(h:Power)[a_,b_],i:{___}]:=Block[{ilist},
ilist=CoefficientList[b,i];
If[Length@ilist<2,"No "<>ToString[i],
If[Length@i==1,a^ilist[[1]] Times@@(\[Delta]/@{ilist[[2]]}),
If[Length@i==2,a^ilist[[1,1]] Times@@(\[Delta]/@{ilist[[2,1]],ilist[[1,2]]}),
If[Length@i==3,a^ilist[[1,1,1]] Times@@(\[Delta]/@{ilist[[2,1,1]],ilist[[1,2,1]],ilist[[1,1,2]]})]]]
]
]
cSumss[(h:Times)[a___],i:{__}]:=h@@(cSumss[#,i]&/@{a})
cSumss[a_,i_]:=a
End[];

cSum[exp_,i_]:=AppToNCM[exp,cfourierPrivateS`cSumss[#,i]&,Identity]

\[Delta][0]:=1;



`privite`AppOperatorsABC[p_Function,f_]:=p@f
`privite`AppOperatorsABC[p_NonCommutativeMultiply,f_]:=Composition[p/.NonCommutativeMultiply->Sequence][f]
AppOperators[exp_,f_]:=AppToNCM[exp,Identity,`privite`AppOperatorsABC[#,f]&]
