# kasami-apn-ab
Formal Lean proofs that the Kasami monomial is APN and AB, and that the related MCM polynomial is a permutation.

## Quick start
Build the project with:

```bash
lake update
lake build
```

## Implementations

- Lean translation of the permutation proof for the MCM polynomial (based on Dobbertin 1998).
- APN property for Kasami monomials: follows directly for odd k; for even k (with odd n) use the standard equivalence between k and n-k.
- Separate translation/implementations: Aristotle‑translated versions and a Dobbertin/Dempwolff/Müller adaptation for odd n.


### AristotleGPT56TerraNagyGP  

The proof of the permutation property of the MCM polynomial has been translated to [Lean](https://lean-lang.org/) by [@Aristotle-Harmonic](https://aristotle.harmonic.fun/). We obtained the APN property of the Kasami monomial using [OpenAI](openai.com)'s GPT-5.6 (Terra version) large language model.

### AristotleNagyGP

The whole proof was translated to [Lean](https://lean-lang.org/) by [@Aristotle-Harmonic](https://aristotle.harmonic.fun/).

### DobbertinDempwolffMuellerOddN

In this component we prove that the MCM polynomial is a permutation when `n` is odd. The argument follows Dempwolff–Müller [DM2013], which is considerably simpler than Dobbertin's original proof.

Consequently, the APN property is established here only for odd `n`.

This work was contributed by [@Aristotle-Harmonic](https://aristotle.harmonic.fun/).

## References

- **[Dob1998]** H. Dobbertin, Kasami power functions, permutation polynomials and cyclic difference sets, in Difference sets, sequences and their correlation properties (Bad Windsheim, 1998), 133–158, NATO Adv. Sci. Inst. Ser. C: Math. Phys. Sci., 542, Kluwer Acad. Publ., Dordrecht; MR1735396
- **[Dob1999]** H. Dobbertin, Another proof of Kasami's theorem, Des. Codes Cryptogr. 17 (1999), no. 1–3, 177–180; MR1714379
- **[DD2004]** J. F. Dillon and H. Dobbertin, New cyclic difference sets with Singer parameters, Finite Fields Appl. 10 (2004), no. 3, 342–389; MR2067603
- **[DM2013]** U. Dempwolff and P. F. Müller, Permutation polynomials and translation planes of even order, Adv. Geom. 13 (2013), no. 2, 293–313; MR3038707
- **[CKM2021]** C. Carlet, K. H. Kim and S. Mesnager, A direct proof of APN-ness of the Kasami functions, Des. Codes Cryptogr. 89 (2021), no. 3, 441–446; MR4220821
