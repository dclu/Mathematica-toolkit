# Mathematica-toolkit

add Pauli Algebra and fermion normal order (facilitate bosonization)
add cfourier, fourier transformation of fermion operator and normal order for fermion and boson.

to use this package, execuate

`URLExecute["https://raw.githubusercontent.com/dclu/Mathematica-toolkit/master/cfourier.m"];`
`URLExecute["https://raw.githubusercontent.com/dclu/Mathematica-toolkit/master/toolkit.m"];`

some examples are in /example/

## toolkit.m
`\sigma s[i,j,k,...]` gives tensor product of several Pauli matrices.

`\sigma find[matrix]` gives the Pauli matrices decomposition of the matrix.

`\sigma Rot` gives the rotation matrix exp(i th/2 \sigma^ijk...)

and so on...

## cfourier.m
The fermion operators are represented by 

`c[d/o,{i,j,k,...},i1,i2,i3,...]`

d / o represents dagger or no dagger,

{i,j,k,...} spacial coordinate,

i1,i2,i3,... band, spin indices.

several operators are represented by non-commutative-multiplication,

`c[d,{i},a]**c[o,{i+1},b]`

`takeDag[ncm poly]` gives Hermitian conjugate of the operators.

`cfourier[ncm poly, dim]` gives the fourier transformation of the operator expression.

`cSum[ncm poly, {i,j,k,...}]` sum over spatial indices and gives delta function.

and so on...