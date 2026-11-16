module

public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The page isomorphisms of the spectral sequence of a spectral object

For a spectral object `X` in an abelian category and spectral sequence data `data`, the
isomorphism `(X.spectralSequence data).iso r r' pq'` between the homology of the `r`-th page at
`pq'` and the `(r + 1)`-th page at `pq'` is the composite of the identification of the homology
with that of the short complex `sc' pq pq' pq''`, the left homology isomorphism of
`X.spectralSequenceHomologyData`, and the inverse of `X.spectralSequencePageXIso` on the page
`r'`.

## Main results

* `MMP.Homology.spectralSequence_iso_eq`: this description of
  `(X.spectralSequence data).iso r r' pq'`.

## Implementation notes

This is `CategoryTheory.Abelian.SpectralObject.spectralSequence_iso`, with the bound
`r₀ ≤ r'` of the page `r'` an explicit hypothesis rather than an automatically filled one, so
that the statement only involves proofs supplied by the caller.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Abelian.SpectralObject

namespace MMP.Homology

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι) {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀) [X.HasSpectralSequence data]

/-- The isomorphism between the homology of the page `r` and the page `r'` of the spectral
sequence of a spectral object, read through `X.spectralSequenceHomologyData`. -/
theorem spectralSequence_iso_eq
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (hr' : r₀ ≤ r')
    (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
    (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
    (hi₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') (hi₁ : i₁ = data.i₁ pq')
    (hi₂ : i₂ = data.i₂ pq') (hi₃ : i₃ = data.i₃ r pq') (hi₃' : i₃' = data.i₃ r' pq')
    (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq') (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (X.spectralSequence data).iso r r' pq' hrr' hr =
      ((X.spectralSequence data).page r hr).homologyIsoSc' pq pq' pq'' hpq hpq' ≪≫
        (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
          i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂).left.homologyIso ≪≫
        (X.spectralSequencePageXIso data r' hr' _ _ _ _ _
          hi₀' hi₁ hi₂ hi₃' _ _ _ hn₁' hn₁ hn₂).symm :=
  X.spectralSequence_iso data r r' hrr' hr pq pq' pq'' hpq hpq' i₀' i₀ i₁ i₂ i₃ i₃'
    hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁' hn₁ hn₂

end MMP.Homology

end
