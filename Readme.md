Formal Verification of Uniswap v3
-----------

This is an unfinished formal verification of Uniswap v3.
Now, we only cover the `swap` module on an abstract specification.
Once our underlying verification platform is completed, we will extend the verification down to the concrete semantics of Solidity, and to cover others modules to finally complete the verification.

A report of the properties we have verified is given [here](https://xqyww123.github.io/Uniswap_v/Unsorted/Uniswap_v/Uniswap_v_Report.html).

## Check the Proof

You can run the verification locally to check the proof.

We use Isabelle-2022 and [φ-System](https://github.com/xqyww123/phi-system). To run the verification, you need first configure φ-System according to the instructions given in the repo.

After configuring φ-System, by changing the work directory to the root of the project, you can run
```
isabelle build -D . Uniswap_v
```
to check the proof.




