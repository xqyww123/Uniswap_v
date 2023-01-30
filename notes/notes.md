1. Do we model GAS?
2. Push() is very tricky!! read `Dangling References to Storage Array Elements`
3. Constant evaluation has arbitrary precision. Is is rational number. `1.5 + 1.5 = 3`, `(1.5**800 + 1) - 1.5**800 = 1`
    https://docs.soliditylang.org/en/v0.8.15/types.html?highlight=Operators#operators
   Suggestion: It must be done during pre-processing, cuz it never generates the code for, like, `1.5 + 1.5`.
               Can we use the constant evaluator of Solidity itself?

Small stuffs, not hard but need attention
1. abi.decode / abi.encodeWithSelector,  .selector
    These are used in Uniswap! https://docs.soliditylang.org/en/v0.8.15/units-and-global-variables.html?highlight=encodewithselector#abi-encoding-and-decoding-functions
2. type expression `type(int32).max` (The uniswap only uses `type(T).max/min`
    https://docs.soliditylang.org/en/v0.8.15/units-and-global-variables.html?highlight=type%20expression#type-information



indeed, our semantic model can support this, by recording the layout on the reference, but the reasoning can be difficult. so i think, we just make it in semantics at most, and 
