# haskell-circuit
circuit diagram emulating in haskell

right now just made combinatorial circuits (no memory)

circuits are based around constant false (ground), NAND gates, and combinations of other combinatorial circuits

capabilities include:
- all the basic logic gates (AND, OR, NOT, ...)
- basic logic gates with variable input sizes
- variable size muxes
- printing truth tables of your circuits
- check the behavior of your circuit against a function of type `[Bool] -> [Bool]`
- make a circuit diagram given a function of type `[Bool] -> [Bool]`
