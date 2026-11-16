module

public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
public import MMP.AlgebraicGeometry.Resolution.Blowup.StrictTransform

/-!
# Restricting blow-up sequences and inverse image ideals to closed subschemes

Let `𝐁 = (X_i, Z_i)` be a blow-up sequence starting with `X` and `S ⊆ X` a closed subscheme. The
restriction `𝐁|_S = (S_i, W_i)` comes with morphisms `j_i : S_i → X_i`, `j_0` the inclusion and
`j_{i+1}` the canonical lift of `j_i` along `Z_i`; each of them is a closed immersion
(Kollár 3.30.2). For one blow-up `π : B_ZX → X` and a morphism `j : H → X`, the canonical
lift `ι : B_ZH → B_ZX` lies over `j`, `π ∘ ι = j ∘ π_H`, so for every ideal sheaf `I ⊆ 𝒪_X` the
restriction of `π^*I` to `B_ZH` is `π_H^*(I|_H)` (Kollár (3.58.2) and the proof of 3.62).

## Main statements

* `MMP.Resolution.Kollar.isClosedImmersion_pullbackHom`: the last morphism `h_r` of the
  pull-back of a blow-up sequence along a closed immersion `h` is a closed immersion.
* `MMP.Resolution.Kollar.isClosedImmersion_restrictHom_truncate`: every `j_i : S_i → X_i` of
  the restriction `𝐁|_S` is a closed immersion.
* `MMP.Resolution.Kollar.comap_canonicalLift_comap_blowUpToBase`: `(π^*I)·𝒪_{B_ZH}` equals
  `π_H^*(I|_H)`.

## Implementation notes

The `i`-th morphism `j_i` of `𝐁|_S` is read on the truncation, as
`(𝐁.truncate i).restrictHom S`; this is legitimate by
`MMP.Resolution.Kollar.pullback_truncate`. For indices beyond the length the truncation is `𝐁`
itself, so the statement is made for every `i`.

In the second statement the source works with a smooth scheme `X`, a smooth hypersurface `H` and
a smooth centre `Z ⊊ H`, and `B_ZH` is the blow-up of `H` along `Z`, embedded in `B_ZX` as the
birational transform of `H`. The identity holds for any morphism `j : H → X`, any closed
subscheme `Z ⊆ X` (with `B_ZH` the blow-up of `H` along `j⁻¹Z`) and any ideal sheaf `I`, and is
stated so. Restriction of an ideal sheaf along a morphism, `J ↦ J·𝒪`, is the inverse image ideal
`Scheme.IdealSheafData.comap`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.30, 3.58, 3.62]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral CategoryTheory.catToReflQuiver

universe u

namespace MMP.Resolution.Kollar

/-- The last morphism `h_r : Y_r → X_r` of the pull-back of a blow-up sequence along a closed
immersion `h : Y → X` is a closed immersion. -/
theorem isClosedImmersion_pullbackHom {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) [IsClosedImmersion h] : IsClosedImmersion (B.pullbackHom h) := by
  induction B generalizing Y with
  | nil X => exact ‹IsClosedImmersion h›
  | cons Z B ih =>
    have := Bridges.isClosedImmersion_canonicalLift h Z
    exact ih (canonicalLift h Z)

/-- **Kollár 3.30.2.** For a blow-up sequence `𝐁` starting with `X` and a closed subscheme
`S ⊆ X`, every morphism `j_i : S_i → X_i` of the restriction `𝐁|_S` is a closed immersion. Here
`j_i` is `(𝐁.truncate i).restrictHom S`, the first `i` steps of `𝐁|_S` being `(𝐁.truncate i)|_S`
by `MMP.Resolution.Kollar.pullback_truncate`. -/
@[mmp "lem_kr3b_restriction_embeddings_closed"]
theorem isClosedImmersion_restrictHom_truncate {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (S : X.IdealSheafData) (i : ℕ) : IsClosedImmersion ((B.truncate i).restrictHom S) :=
  isClosedImmersion_pullbackHom (B.truncate i) S.subschemeι

/-- **Inverse images commute with restriction to `B_ZH`** (Kollár (3.58.2), proof of 3.62). Let
`j : H → X` be a morphism (in the source, the inclusion of a smooth hypersurface), `Z ⊆ X` a
closed subscheme, `π : B_ZX → X` and `π_H : B_{j⁻¹Z}H → H` the blow-ups and
`ι : B_{j⁻¹Z}H → B_ZX` the canonical lift of `j`. Then for every ideal sheaf `I ⊆ 𝒪_X`,
`(π^*I)·𝒪_{B_ZH} = π_H^*(I|_H)`. -/
@[mmp "lem_kr3c_exceptional_divisor_restricts"]
theorem comap_canonicalLift_comap_blowUpToBase {X H : Scheme.{u}} (j : H ⟶ X)
    (Z I : X.IdealSheafData) :
    (I.comap (blowUpToBase Z)).comap (canonicalLift j Z) =
      (I.comap j).comap (blowUpToBase (Z.comap j)) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    canonicalLift_comp_blowUpToBase]

end MMP.Resolution.Kollar
