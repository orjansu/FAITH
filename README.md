# FAITH - a Proof Assistant for Improvement Theory
(a Proo**f** **A**ssistant for **I**mprovement **Th**eory)
Örjan Sunnerhagen 2021

## How to run
1. Build with
    make
2. The executable will be called sie (for Space Improvement Engine, working title). Make it runnable with

        chmod +x sie

3. then run it with

        ./sie <law file> <proof file>

4. Run the first case study with

        ./sie proofFiles/laws/moreLaws.sie proofFiles/proofs/substitution/repeat.hs

5. Run the adding of gadgets to the second case study with

        ./sie proofFiles/laws/moreLaws.sie proofFiles/proofs/substitution/any.sie

6. Run the inductive part of the second case study with

        ./sie proofFiles/laws/moreLaws.sie proofFiles/proofs/substitution/any3.hs

## Master's thesis
The thesis will be published by Chalmers at [Chalmers Open Digital Repository](https://odr.chalmers.se/) soon. Search for the title "Improving Memory Consumption with FAITH - a Proof Assistant for Improvement Theory" by Örjan Sunnerhagen in 2021

## Contact
I will not be actively maintaining this repo, but if you have any questions or comments, you can reach me at orjan.sun (at) gmail (dot) com. I would be very happy if there would be another master's thesis developing FAITH further.
