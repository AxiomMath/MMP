module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionExists
import MMP.AlgebraicGeometry.Singularities.Surface.SingularPointMldBound
import MMP.AlgebraicGeometry.Singularities.GenericSurfacePlaces
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.SNC

/-!
# Positive discrepancies over a codimension-two point force regularity

Let `X` be a normal variety over an algebraically closed field `k` of characteristic zero, `K` a
canonical divisor of `X`, `B ≥ 0` a `ℚ`-divisor with `K + B` `ℚ`-Cartier, and `W ⊆ X` an
irreducible closed subset of codimension two. If every exceptional divisor `E` over `X` with
centre `W` has discrepancy `a(E, X, B) > 0`, then the local ring `𝒪_{X,η_W}` is regular.

Passing to the generic surface germ at `η_W` and its minimal resolution, the discrepancies `aᵢ`
of the exceptional curves satisfy `∑ᵢ aᵢ (Eᵢ · Eⱼ) = (K_Y + B_Y) · Eⱼ ≥ 0`; negative
definiteness of the intersection matrix forces `aᵢ ≤ 0`, so there are no exceptional curves and
the resolution is an isomorphism near the closed point.

## Main results

* `MMP.Mori.isRegularLocalRing_stalk_genericPoint_of_isDiscrepancy_pos`: `𝒪_{X,η_W}` is regular.

## Implementation notes

The source works over `ℂ`; the statement is over any algebraically closed field of
characteristic zero, which is what the argument uses. The discrepancy is the Kollár–Mori one,
`MMP.Mori.IsDiscrepancy`, and "every divisor has positive discrepancy" is stated as: every value
`a` that is a discrepancy of such a divisor is positive.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Exercise 4.9.1
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §4.1
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Mori

/-- Let `X` be a normal variety over an algebraically closed field of characteristic zero with
canonical divisor `K`, let `B ≥ 0` be a `ℚ`-divisor with `K + B` `ℚ`-Cartier, and let `W ⊆ X` be
an irreducible closed subset of codimension two. If every exceptional divisor `D` over `X` with
centre `W` has positive discrepancy `a(D, X, B)`, then `𝒪_{X,η_W}` is a regular local ring. -/
@[mmp "lem_mmp_terminal_codimension_two_regular"]
public theorem isRegularLocalRing_stalk_genericPoint_of_isDiscrepancy_pos {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) {W : IrreducibleCloseds X}
    (hW : codimension W = 2)
    (hpos : ∀ (D : DivisorOver k sX), D.IsExceptional → D.center = W →
      ∀ a : ℚ, IsDiscrepancy sX n K B D a → 0 < a) :
    IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint) := by
  have hP : IsPair sX B := ⟨hX, n, K, hK, hKB⟩
  set x := W.isIrreducible.genericPoint
  have hxW : closure {x} = (W : Set X) := W.isIrreducible.isGenericPoint_genericPoint_closure.trans
    W.isClosed.closure_eq
  have hcx : Order.coheight x = 2 := by
    have hEq : (irreducibleSetEquivPoints (α := X)).symm x = W := IrreducibleCloseds.ext hxW
    rw [← hW, codimension_eq_coheight, ← hEq, Order.coheight_orderIso]
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hdim := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  rw [hxW, hcx, hK.topologicalKrullDim_eq] at hdim
  obtain ⟨d, rfl, hWd⟩ : ∃ d : ℕ, n = d + 2 ∧ topologicalKrullDim (W : Set X) = d := by
    revert hdim
    induction topologicalKrullDim (W : Set X) using WithBot.recBotCoe with
    | bot => intro h; exact absurd h.symm (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        intro h
        rw [← WithBot.coe_add, top_add] at h
        exact absurd h.symm (by exact_mod_cast ENat.coe_ne_top n)
      | coe m =>
        intro h
        refine ⟨m, ?_, rfl⟩
        have h' : ((m + 2 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
          rw [← h]; norm_cast
        exact_mod_cast h'.symm
  obtain ⟨U, -, φ, -, -, S, ι, sS, -, _, _, _, _, hSa, hSft, hSnv, hSdim, p, hp, -, hgen,
    hiso, -, -, BS, hBS, hBS0, -, hbij, hlog⟩ :=
    MMP.Fourfold.exists_genericFibre_bijOn_valuation_center sX ⟨inferInstance, hP, hB⟩
      hK.topologicalKrullDim_eq W hWd
  by_contra hreg
  have hsing : p ∉ smoothLocus sS := by
    intro hps
    apply hreg
    obtain ⟨V, hpV, hV⟩ := mem_smoothLocus_iff.mp hps
    have : Smooth (V.ι ≫ sS) := hV
    have hrV := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ sS) ⟨p, hpV⟩
    have hrS : IsRegularLocalRing (S.presheaf.stalk p) :=
      IsRegularLocalRing.of_ringEquiv (V.stalkIso ⟨p, hpV⟩).commRingCatIsoToRingEquiv
    have hrU : IsRegularLocalRing ((U : Scheme).presheaf.stalk (ι p)) :=
      IsRegularLocalRing.of_ringEquiv (asIso (ι.stalkMap p)).symm.commRingCatIsoToRingEquiv
    have hrX : IsRegularLocalRing (X.presheaf.stalk (U.ι (ι p))) :=
      IsRegularLocalRing.of_ringEquiv (U.stalkIso (ι p)).commRingCatIsoToRingEquiv
    have hxe : U.ι (ι p) = x := hgen.eq hxW
    rwa [hxe] at hrX
  have : IsQuasiProjectiveVariety _ sS := by
    have : AlgebraicGeometry.IsVariety _ sS := hSnv.1
    exact ⟨Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom sS inferInstance⟩
  obtain ⟨D, hDproj, -, hDc, a, ha1, ha⟩ :=
    MMP.Threefold.exists_isLogDiscrepancy_le_one_of_notMem_smoothLocus sS hSdim
      ⟨inferInstance, hBS, hBS0⟩ hp hsing
  have hξ : D.valuation ∈
      {ξ | ∃ D : DivisorOver (FractionRing (MvPolynomial (Fin d) k)) sS,
      D.valuation = ξ ∧ (D.center : Set S) = {p}} := ⟨D, rfl, hDc⟩
  obtain ⟨D₂, hD₂v, hD₂c⟩ := hbij.mapsTo hξ
  obtain ⟨n', D₁, -, hD₁v, hD₁⟩ :=
    (hlog _ hξ a).mp ⟨2, D, isProper_of_isProjectiveMorphism D.f hDproj, rfl, ha⟩
  have hD₁c : D₁.center = W :=
    (MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX.1 (hD₁v.trans hD₂v.symm)).trans hD₂c
  have hD₁e : D₁.IsExceptional := by
    by_contra hne
    obtain ⟨P, hPv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D₁ hne
    exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX D₁).mp
      (by rw [hD₁c, hW]) P hPv
  obtain ⟨a₁, ha₁⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D₁
  have hnn : n' = d + 2 := by
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD₁
    rw [hK.topologicalKrullDim_eq] at this
    exact_mod_cast this.symm
  subst hnn
  have h1 := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha₁ hD₁
  have h2 := hpos D₁ hD₁e hD₁c a₁ ha₁
  have h3 : (0 : ℝ) < a₁ := by exact_mod_cast h2
  linarith

end MMP.Mori
