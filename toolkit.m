(* ::Package:: *)

BeginPackage["toolkit`"]
Commutator::usage="Gives the commutator of matricies.";
AntiCommutator::usage="Gives the anti-commutator of matricies.";
Msig::usage="Judge whether the matrix is zero.";

(*Pauli Matrix *)
\[Sigma]s::usage="Gives Pauli string \!\(\*SuperscriptBox[\(\[Sigma]\), \(ijk ... \)]\)"
\[Sigma]Rot::usage="Gives rotation matrix exp[\[ImaginaryI]\[Theta]/2 \[Sigma]]"
\[Sigma]R4::usage="exp[\[ImaginaryI]\[Pi]/4 \[Sigma]]"
\[Sigma]find::usage="Convert the matrix form to \!\(\*SuperscriptBox[\(\[Sigma]\), \(ijk ... \)]\)"
(*
ExpandNCM::usage="[NCMpoly], Expand NonCommutativeMultiplication"
AppToNCM::usage="[NCM,g,f]Acts on NCM polynomial, g acts on coefficients, f acts on NCM"
takeDag::usage="[NCM] take dagger... g=conjugate, f=reverse"

NCMAntiCommutator::usage="[a,b]Gives Anti-Commutator of NCM"
NCMCommutator::usage="[a,b]Gives Commutator of NCM"
sendNCM::usage="[NCM mononial]"
*)
(*
NOrderB::usage="[NCM] gives boson normal ordering, a[d,...] a[o,...] reps creation/annihilation"
NOrderF::usage="[NCM] gives fermion normal ordering, c[d,...] c[o,...] reps creation/annihilation"
WickCon::usage="[exp,NOrderB/F] wick contraction"
norderB::usage="boson normal ordering"
norderF::usage="boson normal ordering"
*)
AppToCT::usage="Apply function f to CircleTimes, g to coefficients"
PauliEva::usage="Evaluate \[Sigma][]"


Begin["`Private`"];


(* ::Section:: *)
(*Pauli Algebra*)


Commutator[a:{__List},b:{__List}]:=a.b-b.a;
AntiCommutator[a:{__List},b:{__List}]:=a.b+b.a;
Commutator[a_SparseArray,b_SparseArray]:=a.b-b.a;
AntiCommutator[a_SparseArray,b_SparseArray]:=a.b+b.a;
Msig[a:{__List}]:=TrueQ[Total[Abs@Flatten@a]<10^-16];
Msig[a_SparseArray]:=TrueQ[Total[Abs@Flatten@a]<10^-16];


\[Sigma]s[x_]:=PauliMatrix[x]
\[Sigma]s[x__]:=KroneckerProduct@@Map[PauliMatrix,{x}]


\[Sigma]Rot[\[Theta]_,x__]:=MatrixExp[I \[Theta] \[Sigma]s[x]/2]
\[Sigma]R4[x__]:=MatrixExp[I \[Pi]/4 \[Sigma]s[x]]


qubit[m_]:=Log[2,Length[m]]
\[Sigma]find[m_]:=Block[{qub,\[Sigma]table,tup},
qub=qubit[m];
If[qub\[Element]Integers,

tup=Tuples[Range[0,3],qub];
\[Sigma]table=\[Sigma]s@@@tup;
\[Sigma]table=(ArrayReshape[#,{2^qub 2^qub,1}]&/@\[Sigma]table);
Total[1/2^qub Flatten@Table[Total[(ConjugateTranspose@ArrayReshape[m,{4^qub,1}].\[Sigma]table[[i]])]Superscript["\[Sigma]",tup[[i]]],{i,Length@\[Sigma]table}]]
]
]


(* ::Subsection:: *)
(*symbolic*)


Clear[sendCT,expandCT]
(*a[__] to represent fermion/boson operator, d/o represent dagger or not*)
expandCT[(h:CircleTimes)[a___,b_Plus,c___]]:=Distribute[h[a,b,c],Plus,h,Plus,expandCT[h[##]]&]
expandCT[(h:CircleTimes)[a___,b_Times,c___]]:=Most[b]expandCT[h[a,Last[b],c]]
expandCT[a_]:=ExpandAll[a]
ExpandCT[exp_]:=Block[{exp1},
exp1=expandCT[exp];
Distribute[fggsfsf[exp1]]/.fggsfsf->expandCT
]
(*g acts on coefficients, f acts on NonCM*)
sendCT[(h:Times)[a___,b_CircleTimes],g_,f_]:=g[Times[a]]f[b]
sendCT[(h:Times)[a___,b_CircleTimes,c__],g_,f_]:=g[Times[a,c]]f[b]
sendCT[b_CircleTimes,g_,f_]:=f[b]
sendCT[(h:Times)[a___,\[Sigma][k___]],g_,f_]:=g[Times[a]]f[\[Sigma][k]]
sendCT[\[Sigma][k___],g_,f_]:=f[\[Sigma][k]]
sendCT[a_?NumberQ,g_,f_]:=g[a]
(*sendNCM[(h:Times)[tt___,a[k___]],g_,f_]:=g[Times[tt]]f[a[k]]
sendNCM[a[k___],g_,f_]:=f[a[k]]
sendNCM[ff_Function,g_,f_]:=f[ff]
sendNCM[(h:Times)[tt___,ff_Function],g_,f_]:=g[Times[tt]]f[ff]*)

AppToCT[exp_,g_,f_]:=Distribute[sendCT[ExpandCT[exp],g,f]]


Clear[EvaPauli,IndexProduct,PauliEva]
IndexProduct[0,i_]:=i;
IndexProduct[i_,0]:=i;
IndexProduct[i_,i_]:=0;
IndexProduct[1,2]:=(Sow[I];3);
IndexProduct[2,3]:=(Sow[I];1);
IndexProduct[3,1]:=(Sow[I];2);
IndexProduct[2,1]:=(Sow[-I];3);
IndexProduct[3,2]:=(Sow[-I];1);
IndexProduct[1,3]:=(Sow[-I];2);
IndexProduct[i_,j_,k__]:=IndexProduct[IndexProduct[i,j],k]
EvaPauli[(h:CircleTimes)[As:_\[Sigma]..]]:=Times@@Flatten@Reap[IndexProduct@@@Thread[{As},\[Sigma]]]
EvaPauli[(h:CircleTimes)[___,0,___]]:=0
PauliEva[exp_]:=AppToCT[exp,Identity,EvaPauli]


(* ::Section::Closed:: *)
(*Non-commutative algebra*)


(*
ClearAll[ExpandNCM,sendNCM,AppToNCM,takeDag,NCMAntiCommutator,NCMCommutator]
(*a[__] to represent fermion/boson operator, d/o represent dagger or not*)
ExpandNCM[(h:NonCommutativeMultiply)[a___,b_Plus,c___]]:=Distribute[h[a,b,c],Plus,h,Plus,ExpandNCM[h[##]]&]
ExpandNCM[(h:NonCommutativeMultiply)[a___,b_Times,c___]]:=Most[b]ExpandNCM[h[a,Last[b],c]]
ExpandNCM[a_]:=ExpandAll[a]
(*g acts on coefficients, f acts on NonCM*)
sendNCM[(h:Times)[a___,b_NonCommutativeMultiply],g_,f_]:=g[Times[a]]f[b]
sendNCM[b_NonCommutativeMultiply,g_,f_]:=f[b]

AppToNCM[exp_,g_,f_]:=Distribute[sendNCM[ExpandNCM[exp],g,f]]
takeDag[exp_]:=AppToNCM[exp,Conjugate,Reverse]/.{d->o,o->d}

NCMAntiCommutator[a_,b_]:=a**b+b**a
NCMCommutator[a_,b_]:=a**b-b**a
*)


(* ::Section:: *)
(*end*)


End[];
EndPackage[]
