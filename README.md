# On the selection of weights for difference schemes approximating systems of differential equations

1. [Finding coefficients](#finding-coefficients)
2. [Numerical experiments](#numerical-experiments)

## Finding coefficients

Defining a scheme:
```python
sage: load("dps.sage")
sage: s = Scheme([x,t],[f,L], param, rk4(), order = 4)
```

## Numerical experiments

For using dps() function you should import [fdm](https://github.com/malykhmd/fdm) package. 
In IPython Notebook:
```python
%%capture
!git clone https://github.com/malykhmd/fdm
%cd fdm
load('fdm.sage')
%cd ..
!rm -rf fdm/ 
```
