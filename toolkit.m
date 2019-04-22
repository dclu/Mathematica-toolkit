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


Begin["`Private`"];


(* ::Section:: *)
(*Pauli Algebra*)


Commutator[a:{{__},{__}},b:{{__},{__}}]:=a.b-b.a;
AntiCommutator[a:{{__},{__}},b:{{__},{__}}]:=a.b+b.a;
Commutator[a_SparseArray,b_SparseArray]:=a.b-b.a;
AntiCommutator[a_SparseArray,b_SparseArray]:=a.b+b.a;
Msig[a:{{__},{__}}]:=TrueQ[Total[Abs@Flatten@a]<10^-16];
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


(* ::Section:: *)
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
