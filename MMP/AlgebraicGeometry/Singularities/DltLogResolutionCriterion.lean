module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres

/-!
# Log resolutions and dlt pairs: discrepancy near zero, disjoint transforms, the dlt criterion

For a pair `(X, Δ)` over an algebraically closed field of characteristic zero, this file proves
three consequences of the existence of log resolutions (Kollár–Mori 2.32, 2.40): near `ε = 0`
the discrepancy of `(X, Δ + εΔ')` is a minimum of finitely many affine functions of `ε`; there
is a log resolution on which the birational transforms of the components of `Δ` are smooth and
pairwise disjoint; and `(X, Δ)` is dlt exactly when the discrepancy condition can be checked on
the divisors of one log resolution lying over a closed subset outside of which the pair is snc.

## Main results

* `MMP.Mori.exists_discrep_add_smul_eq_inf'`: `discrep(X, Δ + εΔ')` is, for small rational
  `ε ≥ 0`, the minimum of finitely many affine functions of `ε`, equal to `discrep(X, Δ)` at `0`.
* `MMP.Mori.exists_isLogResolution_disjoint_inverseTransformPrimeDivisor`: a log resolution of
  `(X, Δ)` whose birational transforms of the components of `Δ` are smooth and pairwise disjoint.
* `MMP.Mori.isDltPair_iff_exists_isLogResolution`: the criterion for dlt pairs on one log
  resolution (Kollár–Mori 2.40, with the snc condition on `Ex(f) ∪ f⁻¹(Supp Δ) ∪ f⁻¹(Z)`).

## Implementation notes

Each result's auxiliary lemmas live in a namespace `Proof_<tag>` named after its label,
opened only for that result. The affine functions are affine maps `ℚ →ᵃ[ℚ] ℚ` and their minimum
is `Finset.inf'`; the discrepancy is valued in `EReal`. The disjoint transforms are obtained by
blowing up, one at a time, the components of pairwise intersections of the transforms, with the
number of such components as induction measure.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 2.32,
  Proposition 2.40
-/

@[expose] public section

universe u

namespace Proof_lem_km2b_discrep_near_zero

open CategoryTheory MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor

/-- The affine map `ε ↦ a + b ε` of `ℚ`. -/
private def affineOf (a b : ℚ) : ℚ →ᵃ[ℚ] ℚ := AffineMap.const ℚ ℚ a + b • AffineMap.id ℚ ℚ

private theorem affineOf_apply (a b ε : ℚ) : affineOf a b ε = a + b * ε := by
  simp [affineOf]

/-- The components of an snc subset form a finite set of prime divisors with snc reduced sum. -/
private theorem exists_finset_isSNC {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation sY]
    (hsm : IsSmoothScheme sY) {T : TopologicalSpace.Closeds Y} (hT : IsSNCSubset sY T) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor Y),
      DivisorWithCoeffs.IsSNC sY (∑ E ∈ S, Finsupp.single E (1 : ℤ)) ∧
      ∀ F : MMP.Mori.PrimeDivisor Y, F.genericPoint ∈ (T : Set Y) → F ∈ S := by
  rcases hT with h0 | ⟨s, hs, hsnc⟩
  · refine ⟨∅, ?_, fun F hF => ?_⟩
    · rw [Finset.sum_empty]
      exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hsm
    · simp [h0] at hF
  · refine ⟨s, hsnc, fun F hF => ?_⟩
    rw [← hs] at hF
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hF
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE

/-- A prime divisor of a proper birational model that is not exceptional maps generically onto a
prime divisor `P` of `X`, and its coefficient in the crepant boundary is `coeff_P Δ`. -/
private theorem exists_coeff_eq_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hP : IsPairWith sX n K Δ) {f : Y ⟶ X} (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, ΔY.coeff G = Δ.coeff P ∧
      f G.genericPoint = P.genericPoint := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hG
  have hη : f G.genericPoint = P.genericPoint := by
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact ⟨P, neg_injective ((hΔY G).eq hd), hη⟩

/-- A non-exceptional prime divisor `G` of a model, mapping onto the prime divisor `P` of `X`, has
coefficients `coeff_P Δ` and `coeff_P Δ'` in the crepant boundaries `Θ` of `(X, Δ)` and `Θ + B`
of `(X, Δ + Δ')`. -/
private theorem exists_coeff_eq_coeff_eq_of_not_isExceptional {k : Type u} [Field k]
    [PerfectField k] {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ Δ' : QDivisor X}
    (hP : IsPairWith sX n K Δ) (hP' : IsPairWith sX n K (Δ + Δ')) {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {Θ B : QDivisor Y}
    (hΘ : IsCrepantBoundary sX n K Δ f hY hf Θ)
    (hΘ' : IsCrepantBoundary sX n K (Δ + Δ') f hY hf (Θ + B)) {G : MMP.Mori.PrimeDivisor Y}
    (hG : ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, Θ.coeff G = Δ.coeff P ∧ B.coeff G = Δ'.coeff P ∧
      f G.genericPoint = P.genericPoint := by
  obtain ⟨P, hc0, hη⟩ := exists_coeff_eq_of_not_isExceptional hP hY hf hΘ hG
  obtain ⟨P', hc1, hη'⟩ := exists_coeff_eq_of_not_isExceptional hP' hY hf hΘ' hG
  obtain rfl : P' = P :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hη'.symm.trans hη)
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add] at hc1
  exact ⟨P', hc0, by linarith, hη⟩

/-- A function positive on the members of a finite set satisfying `p` has a uniform positive
lower bound there. -/
private theorem exists_pos_forall_le {α : Type*} (s : Finset α) (p : α → Prop) (g : α → ℚ)
    (h : ∀ x ∈ s, p x → 0 < g x) : ∃ ε : ℚ, 0 < ε ∧ ∀ x ∈ s, p x → ε ≤ g x := by
  classical
  refine ⟨(insert 1 ((s.filter p).image g)).min' (Finset.insert_nonempty _ _), ?_,
    fun x hx hpx => Finset.min'_le _ _ (by simpa using Or.inr ⟨x, ⟨hx, hpx⟩, rfl⟩)⟩
  simpa [Finset.lt_min'_iff] using fun _ x hx hpx hgx => hgx ▸ h x hx hpx

/-- If `θ_G ≤ 1` on a finite set, with `δ_G = 0` wherever `θ_G = 1`, then `θ_G + ε δ_G ≤ 1` on it
for all small `ε ≥ 0`. -/
private theorem exists_pos_forall_add_mul_le_one {ι : Type*} (S : Finset ι) (θ δ : ι → ℚ)
    (hθ : ∀ G ∈ S, θ G ≤ 1) (hθδ : ∀ G ∈ S, θ G = 1 → δ G = 0) :
    ∃ ε₁ : ℚ, 0 < ε₁ ∧ ∀ ε : ℚ, 0 ≤ ε → ε < ε₁ → ∀ G ∈ S, θ G + ε * δ G ≤ 1 := by
  obtain ⟨ε₁, hε₁, hle⟩ := exists_pos_forall_le S (fun G => 0 < δ G) (fun G => (1 - θ G) / δ G)
    fun G hG hδ => div_pos (sub_pos.2 <| (hθ G hG).lt_of_ne fun h => (hθδ G hG h ▸ hδ).false) hδ
  refine ⟨ε₁, hε₁, fun ε hε hεε G hG => ?_⟩
  rcases le_or_gt (δ G) 0 with hδ | hδ
  · nlinarith [hθ G hG]
  · have := (lt_div_iff₀ hδ).1 (hεε.trans_le (hle G hG hδ))
    linarith

/-- The affine functions of the snc formula on a model: the constant `1`, `1 - θ_G - εδ_G` for
`G ∈ S`, `1 - θ_G - θ_F - ε(δ_G + δ_F)` for distinct meeting `G, F ∈ S`, and `-θ_E - εδ_E` for
exceptional `E ∈ S`. -/
private noncomputable def affineFamily {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (meet : ι → ι → Prop) [DecidableRel meet] (exc : ι → Prop) [DecidablePred exc] (θ δ : ι → ℚ) :
    Finset (ℚ →ᵃ[ℚ] ℚ) :=
  haveI := Classical.decEq (ℚ →ᵃ[ℚ] ℚ)
  insert (affineOf 1 0) (S.image (fun G => affineOf (1 - θ G) (-δ G)) ∪
    ((S ×ˢ S).filter fun p => p.1 ≠ p.2 ∧ meet p.1 p.2).image
      (fun p => affineOf (1 - θ p.1 - θ p.2) (-(δ p.1 + δ p.2))) ∪
    (S.filter exc).image fun G => affineOf (-θ G) (-δ G))

private theorem affineFamily_nonempty {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (meet : ι → ι → Prop) [DecidableRel meet] (exc : ι → Prop) [DecidablePred exc]
    (θ δ : ι → ℚ) : (affineFamily S meet exc θ δ).Nonempty := by
  classical exact ⟨affineOf 1 0, by simp [affineFamily]⟩

/-- The minimum of `affineFamily` at `ε` is the snc formula on the model, with coefficients
`θ_G + εδ_G`, together with the discrepancies `-θ_E - εδ_E` of the exceptional divisors. -/
private theorem coe_inf'_affineFamily {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (meet : ι → ι → Prop) [DecidableRel meet] (exc : ι → Prop) [DecidablePred exc]
    (θ δ : ι → ℚ) (ε : ℚ) :
    ((((affineFamily S meet exc θ δ).inf' (affineFamily_nonempty S meet exc θ δ)
        fun ℓ => ℓ ε : ℚ) : ℝ) : EReal) =
      (⨅ (E ∈ S) (F ∈ S) (_ : E ≠ F) (_ : meet E F),
          (((1 - (θ E + ε * δ E) - (θ F + ε * δ F) : ℚ) : ℝ) : EReal)) ⊓
        (⨅ E ∈ S, (((1 - (θ E + ε * δ E) : ℚ) : ℝ) : EReal)) ⊓ 1 ⊓
        ⨅ E ∈ S, ⨅ (_ : exc E), (((-(θ E + ε * δ E) : ℚ) : ℝ) : EReal) := by
  classical
  set L := affineFamily S meet exc θ δ
  have hv : ∀ ℓ ∈ L, ∀ q : ℚ, ℓ ε = q →
      (((L.inf' (affineFamily_nonempty S meet exc θ δ) fun ℓ => ℓ ε : ℚ) : ℝ) : EReal) ≤
        ((q : ℝ) : EReal) := fun ℓ hℓ q hq => by
    rw [← hq]
    exact_mod_cast Finset.inf'_le _ hℓ
  refine le_antisymm (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_) ?_
  · exact le_iInf₂ fun G hG => le_iInf₂ fun F hF => le_iInf₂ fun hGF hmeet =>
      hv _ (by
        unfold L affineFamily
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (a := (G, F))
            (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hG, hF⟩, hGF, hmeet⟩)))))
        _ (by rw [affineOf_apply]; ring)
  · exact le_iInf₂ fun G hG => hv _ (by
      unfold L affineFamily
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ hG)))) _ (by rw [affineOf_apply]; ring)
  · exact_mod_cast hv _ (by unfold L affineFamily; exact Finset.mem_insert_self _ _) 1
      (by simp [affineOf_apply])
  · exact le_iInf₂ fun G hG => le_iInf fun hGe => hv _ (by
      unfold L affineFamily
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hG, hGe⟩)))) _
      (by rw [affineOf_apply]; ring)
  obtain ⟨ℓ, hℓ, heq⟩ := Finset.exists_mem_eq_inf' (affineFamily_nonempty S meet exc θ δ)
    fun ℓ => ℓ ε
  rw [heq]
  simp only [L, affineFamily, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_product] at hℓ
  rcases hℓ with
    rfl | ((⟨G, hG, rfl⟩ | ⟨⟨G, F⟩, ⟨⟨hG, hF⟩, hGF, hmeet⟩, rfl⟩) | ⟨G, ⟨hG, hGe⟩, rfl⟩)
  · exact inf_le_left.trans (inf_le_right.trans_eq (by simp [affineOf_apply]))
  · refine inf_le_left.trans (inf_le_left.trans (inf_le_right.trans
      ((iInf₂_le G hG).trans_eq ?_)))
    rw [affineOf_apply]
    congr 2
    ring
  · refine inf_le_left.trans (inf_le_left.trans (inf_le_left.trans ((iInf₂_le G hG).trans
      ((iInf₂_le F hF).trans ((iInf₂_le hGF hmeet).trans_eq ?_)))))
    rw [affineOf_apply]
    congr 2
    ring
  · refine inf_le_right.trans ((iInf₂_le G hG).trans ((iInf_le _ hGe).trans_eq ?_))
    rw [affineOf_apply]
    congr 2
    ring

end Proof_lem_km2b_discrep_near_zero

namespace MMP.Mori

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor
open Proof_lem_km2b_discrep_near_zero

private theorem coeff_sum_single_ne_zero {X : Scheme.{u}} {s : Finset (MMP.Mori.PrimeDivisor X)}
    {P : MMP.Mori.PrimeDivisor X} (hP : P ∈ s) :
    (∑ Q ∈ s, Finsupp.single Q (1 : ℝ) : RDivisor X).coeff P ≠ 0 := by
  classical
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply, hP]

/-- **The discrepancy near `ε = 0`** (Kollár–Mori 2.32). Let `(X, Δ)` be a pair with canonical
divisor `K` of dimension `n ≥ 2` over an algebraically closed field of characteristic zero, with
`discrep(X, Δ) > -1` and `coeff_P Δ ≤ 1` for every prime divisor `P`, and let `Δ'` be a
`ℚ`-Cartier `ℚ`-divisor with `coeff_P Δ' = 0` whenever `coeff_P Δ = 1`. Then there are a rational
`ε₁ > 0` and a nonempty finite set `L` of affine maps `ℚ → ℚ` with `min_{ℓ ∈ L} ℓ 0 =
discrep(X, Δ)` and `discrep(X, Δ + εΔ') = min_{ℓ ∈ L} ℓ ε` for every rational `0 ≤ ε < ε₁`. -/
@[mmp "lem_km2b_discrep_near_zero"]
public theorem exists_discrep_add_smul_eq_inf' {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hP : IsPairWith sX n K Δ) (hn : 2 ≤ n) (hd : -1 < discrep sX n K Δ)
    (hΔ : ∀ P : PrimeDivisor X, Δ.coeff P ≤ 1) {Δ' : QDivisor X} (hΔ' : Δ'.IsQCartier)
    (h0 : ∀ P : PrimeDivisor X, Δ.coeff P = 1 → Δ'.coeff P = 0) :
    ∃ ε₁ : ℚ, 0 < ε₁ ∧ ∃ (L : Finset (ℚ →ᵃ[ℚ] ℚ)) (hL : L.Nonempty),
      discrep sX n K Δ = (((L.inf' hL fun ℓ => ℓ 0 : ℚ) : ℝ) : EReal) ∧
      ∀ ε : ℚ, 0 ≤ ε → ε < ε₁ →
        discrep sX n K (Δ + ε • Δ') = (((L.inf' hL fun ℓ => ℓ ε : ℚ) : ℝ) : EReal) := by
  classical
  have hX : IsNormalVariety k sX := hP.1
  let A : RDivisor X := ∑ P ∈ Δ.support ∪ Δ'.support, Finsupp.single P (1 : ℝ)
  obtain ⟨Y, f, hf⟩ := exists_isLogResolution sX hX A
  obtain ⟨hY, hdimY, -⟩ := hf.toIsSmoothResolution.isNormalVariety hX
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsNormal Y := hY.2
  have : IsProper f := hf.isProper
  have : MMP.Mori.IsVariety k sX := hX.1
  have : MMP.Mori.IsVariety k (f ≫ sX) := hY.1
  have : IsDominant f := hf.isBirationalMorphism.isDominant
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  set hfb := hf.isBirationalMorphism
  let DG : MMP.Mori.PrimeDivisor Y → DivisorOver k sX := fun G => ⟨Y, f, hY, hfb, G⟩
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hf.isSmoothScheme
    (hdimY.trans hP.2.1.topologicalKrullDim_eq)
  have hpair : ∀ ε : ℚ, IsPairWith sX n K (Δ + ε • Δ') := fun ε =>
    ⟨hX, hP.2.1, by
      rw [← add_assoc]
      exact hP.2.2.add (MMP.Flips.isQCartier_smul hΔ' ε)⟩
  obtain ⟨⟨Θ, hΘ, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP.isPair hP.2.1 f hY hfb
  have hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ Δ'.supp := by
    intro Z
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint,
      map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp Δ'
  set B' : QDivisor Y := QDivisor.pullback (f := f) Δ' hΔ' hB
  set θ : MMP.Mori.PrimeDivisor Y → ℚ := Θ.coeff
  set δ : MMP.Mori.PrimeDivisor Y → ℚ := B'.coeff
  have hc : ∀ (ε : ℚ) G, (Θ + ε • B').coeff G = θ G + ε * δ G := fun ε G => by
    simp [θ, δ, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul]
  have hline : ∀ (ε : ℚ) (G : MMP.Mori.PrimeDivisor Y),
      IsDiscrepancy sX n K (Δ + ε • Δ') (DG G) (-(θ G + ε * δ G)) := by
    intro ε G
    obtain ⟨-, _, hiff⟩ := hP.isDiscrepancy_add_smul_iff hΔ' (DG G)
    convert ((hiff B' (QDivisor.isPullback_pullback hΔ' hB)).2 ε (-θ G)).mpr (hΘ G) using 1
    simp only [θ, δ, DG]
    ring
  have hΘε : ∀ ε : ℚ, IsCrepantBoundary sX n K (Δ + ε • Δ') f hY hfb (Θ + ε • B') :=
    fun ε G => by simpa [hc] using hline ε G
  obtain ⟨S, hsncS, hmemS⟩ :=
    exists_finset_isSNC hf.isSmoothScheme hf.isSNCSubset
  have hexcS : ∀ G : MMP.Mori.PrimeDivisor Y, (DG G).IsExceptional → G ∈ S := fun G hG =>
    hmemS G (Or.inl (MMP.Positivity.support_subset_exceptionalSet G hG
      (MMP.Flips.primeDivisor_genericPoint_mem_support G)))
  have hexc : ∀ G, (DG G).IsExceptional → θ G < 1 := fun G hG => by
    have := lt_of_lt_of_le hd (discrep_le hG (hΘ G))
    have : ((θ G : ℝ) : EReal) < ((1 : ℝ) : EReal) := by simpa using this
    exact_mod_cast EReal.coe_lt_coe_iff.mp this
  have hnexc : ∀ G, ¬ (DG G).IsExceptional → ∃ P : MMP.Mori.PrimeDivisor X,
      θ G = Δ.coeff P ∧ δ G = Δ'.coeff P ∧ f G.genericPoint = P.genericPoint := fun G hG =>
    exists_coeff_eq_coeff_eq_of_not_isExceptional (Δ' := Δ') (B := B') hP
      (by simpa using hpair 1) hY hfb hΘ (by simpa using hΘε 1) hG
  have hsuppS : ∀ G, (θ G ≠ 0 ∨ δ G ≠ 0) → G ∈ S := by
    intro G hG0
    by_cases hG : (DG G).IsExceptional
    · exact hexcS G hG
    obtain ⟨P, hθP, hδP, hη⟩ := hnexc G hG
    have hmem : P ∈ Δ.support ∪ Δ'.support := by
      rw [hθP, hδP] at hG0
      rwa [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    refine hmemS G (Or.inr ?_)
    change f G.genericPoint ∈ A.supp
    rw [hη]
    exact DivisorWithCoeffs.support_subset_supp (coeff_sum_single_ne_zero hmem)
      (MMP.Flips.primeDivisor_genericPoint_mem_support P)
  obtain ⟨ε₁, hε₁, hcoeff⟩ := exists_pos_forall_add_mul_le_one S θ δ
    (fun G _ => by
      by_cases hG : (DG G).IsExceptional
      · exact (hexc G hG).le
      · obtain ⟨P, hθP, -, -⟩ := hnexc G hG
        exact hθP ▸ hΔ P)
    (fun G _ h1 => by
      by_cases hG : (DG G).IsExceptional
      · exact absurd h1 (hexc G hG).ne
      · obtain ⟨P, hθP, hδP, -⟩ := hnexc G hG
        exact hδP ▸ h0 P (hθP ▸ h1))
  have key : ∀ ε : ℚ, 0 ≤ ε → ε < ε₁ →
      discrep sX n K (Δ + ε • Δ') = ((((affineFamily S
        (fun G F => (G.support ∩ F.support).Nonempty) (fun G => (DG G).IsExceptional) θ δ).inf'
          (affineFamily_nonempty ..) fun ℓ => ℓ ε : ℚ) : ℝ) : EReal) := by
    intro ε hε hεε
    have hsuppε : (Θ + ε • B').support ⊆ S := fun G hG => hsuppS G <| by
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hc] at hG
      contrapose! hG
      simp [hG.1, hG.2]
    rw [IsCrepantBoundary.discrep_eq_min (hpair ε).isPair hP.2.1 hKY (hΘε ε),
      discrep_eq_of_isSNC (f ≫ sX) hY hf.isSmoothScheme hn hKY S hsuppε hsncS
        (fun G hG => hc ε G ▸ hcoeff ε hε hεε G hG), coe_inf'_affineFamily]
    simp only [hc]
    congr 1
    refine le_antisymm (le_iInf₂ fun E _ => le_iInf fun hE =>
      sInf_le ⟨E, _, hE, hline ε E, rfl⟩) (le_sInf ?_)
    rintro _ ⟨E, a, hE, ha, rfl⟩
    exact (iInf₂_le E (hexcS E hE)).trans ((iInf_le _ hE).trans_eq (by rw [ha.eq (hline ε E)]))
  exact ⟨ε₁, hε₁, _, affineFamily_nonempty .., by simpa using key 0 le_rfl hε₁, key⟩

end MMP.Mori

namespace Proof_lem_km2b_log_resolution_disjoint_boundary_transforms

open CategoryTheory TopologicalSpace MMP.Mori MMP.Resolution
open AlgebraicGeometry hiding PrimeDivisor

/-- The support of the birational transform `f⁻¹_* D`, or `∅` when it is undefined. -/
private noncomputable def tsupp {X Y : Scheme.{u}} (f : Y ⟶ X) (D : MMP.Mori.PrimeDivisor X) :
    Set Y :=
  ((inverseTransformPrimeDivisor f D).map fun E => (E.support : Set Y)).getD ∅

private theorem tsupp_eq {X Y : Scheme.{u}} {f : Y ⟶ X} {D : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : inverseTransformPrimeDivisor f D = some E) :
    tsupp f D = E.support := by
  simp [tsupp, h]

/-- The number of irreducible components of the pairwise intersections of the transforms. -/
private noncomputable def measure {X Y : Scheme.{u}} (𝒟 : Finset (MMP.Mori.PrimeDivisor X))
    (f : Y ⟶ X) : ℕ :=
  ∑ p ∈ 𝒟.offDiag, (componentsOf (tsupp f p.1 ∩ tsupp f p.2)).ncard

/-- A point lies on a prime divisor exactly when it specializes its generic point. -/
private theorem mem_support_iff_specializes {Y : Scheme.{u}} (E : MMP.Mori.PrimeDivisor Y)
    {x : Y} : x ∈ (E.support : Set Y) ↔ E.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, specializes_iff_mem_closure]

/-- A variety over a field is a Noetherian topological space. -/
private theorem noetherianSpace_of_isVariety {k : Type u} [Field k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (h : MMP.Mori.IsVariety k s) : NoetherianSpace Y :=
  have : LocallyOfFiniteType s := h.toLocallyOfFiniteType
  Aux.noetherianSpace_of_finiteType s

private theorem mem_support_sum_single {Y : Scheme.{u}} {s : Finset (MMP.Mori.PrimeDivisor Y)}
    {F : MMP.Mori.PrimeDivisor Y} (hF : F ∈ s) :
    F ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support := by
  classical
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply, hF]

/-- The prime divisors of the support of `Δ` lie in `Supp Δ`. -/
private theorem support_subset_supp_toRDivisor {X : Scheme.{u}} {Δ : QDivisor X}
    {D : MMP.Mori.PrimeDivisor X} (hD : D ∈ Δ.support) :
    (D.support : Set X) ⊆ (QDivisor.toRDivisor Δ).supp := by
  refine DivisorWithCoeffs.support_subset_supp ?_
  rw [QDivisor.coeff_toRDivisor]
  exact_mod_cast Finsupp.mem_support_iff.mp hD

/-- For a log resolution `f` of `(X, Δ)` and a family `s` of prime divisors whose union is
`Ex(f) ∪ f⁻¹(Supp Δ)`, the transform of a component of `Δ` belongs to `s`. -/
private theorem mem_of_iUnion_eq {X Y : Scheme.{u}} {Δ : QDivisor X} {f : Y ⟶ X}
    {s : Finset (MMP.Mori.PrimeDivisor Y)}
    (hs : (⋃ F ∈ s, (F.support : Set Y)) =
      ↑(exceptionalSet f ⊔ (QDivisor.toRDivisor Δ).supp.preimage f.continuous))
    {D : MMP.Mori.PrimeDivisor X} (hD : D ∈ Δ.support) {E : MMP.Mori.PrimeDivisor Y}
    (hE : inverseTransformPrimeDivisor f D = some E) : E ∈ s := by
  have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hE).1
  have hmem : E.genericPoint ∈ ⋃ F ∈ s, (F.support : Set Y) := by
    rw [hs]
    right
    change f E.genericPoint ∈ ((QDivisor.toRDivisor Δ).supp : Set X)
    rw [hη]
    exact support_subset_supp_toRDivisor hD (MMP.Flips.primeDivisor_genericPoint_mem_support D)
  obtain ⟨F, hF, hEF⟩ := Set.mem_iUnion₂.mp hmem
  have := F.eq_genericPoint_of_mem_support hEF E.coheight_genericPoint
  rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_injective this]

/-- For a log resolution `f` of `(X, Δ)`, the transform of a component of `Δ` is a component of
the snc divisor `Ex(f) ∪ f⁻¹(Supp Δ)`. -/
private theorem exists_snc_family {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {Δ : QDivisor X} {f : Y ⟶ X}
    (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f) {D : MMP.Mori.PrimeDivisor X}
    (hD : D ∈ Δ.support) {E : MMP.Mori.PrimeDivisor Y}
    (hE : inverseTransformPrimeDivisor f D = some E) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor Y),
      (⋃ F ∈ s, (F.support : Set Y)) =
        ↑(exceptionalSet f ⊔ (QDivisor.toRDivisor Δ).supp.preimage f.continuous) ∧
      DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ F ∈ s, Finsupp.single F (1 : ℤ)) ∧ E ∈ s := by
  rcases hf.isSNCSubset with h0 | ⟨s, hs, hsnc⟩
  · have := mem_of_iUnion_eq (s := ∅) (by rw [h0]; simp) hD hE
    simp at this
  exact ⟨s, hs, hsnc, mem_of_iUnion_eq hs hD hE⟩

/-- If every element of `S` is related to some element of the finite set `T`, and no two
distinct elements of `S` are related to a common one, then `#S ≤ #T`. -/
private theorem ncard_le_of_rel {α β : Type*} {S : Set α} {T : Set β} (hT : T.Finite)
    (R : α → β → Prop) (hex : ∀ a ∈ S, ∃ b ∈ T, R a b)
    (huniq : ∀ a ∈ S, ∀ a' ∈ S, ∀ b ∈ T, R a b → R a' b → a = a') :
    S.ncard ≤ T.ncard := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  obtain ⟨b₀, -, -⟩ := hex a₀ ha₀
  have : Nonempty β := ⟨b₀⟩
  let φ : α → β := fun a => Classical.epsilon fun b => b ∈ T ∧ R a b
  have hφ : ∀ a ∈ S, φ a ∈ T ∧ R a (φ a) := fun a ha => by
    obtain ⟨b, hb, hab⟩ := hex a ha
    exact Classical.epsilon_spec (p := fun b => b ∈ T ∧ R a b) ⟨b, hb, hab⟩
  refine Set.ncard_le_ncard_of_injOn φ (fun a ha => (hφ a ha).1) (fun a ha a' ha' he => ?_) hT
  exact huniq a ha a' ha' _ (hφ a ha).1 (hφ a ha).2 (he ▸ (hφ a' ha').2)

/-- The strict version of `ncard_le_of_rel`, when some element of `T` is related to nothing. -/
private theorem ncard_lt_of_rel {α β : Type*} {S : Set α} {T : Set β} (hT : T.Finite)
    (R : α → β → Prop) (hex : ∀ a ∈ S, ∃ b ∈ T, R a b)
    (huniq : ∀ a ∈ S, ∀ a' ∈ S, ∀ b ∈ T, R a b → R a' b → a = a') {b₀ : β} (hb₀ : b₀ ∈ T)
    (hR : ∀ a ∈ S, ¬ R a b₀) :
    S.ncard < T.ncard := by
  refine lt_of_le_of_lt (ncard_le_of_rel (hT.diff) R (fun a ha => ?_)
    (fun a ha a' ha' b hb => huniq a ha a' ha' b hb.1)) (Set.ncard_diff_singleton_lt_of_mem hb₀ hT)
  obtain ⟨b, hb, hab⟩ := hex a ha
  exact ⟨b, ⟨hb, fun h => hR a ha (Set.mem_singleton_iff.mp h ▸ hab)⟩, hab⟩

/-- An irreducible component of a closed subset of a scheme has a generic point. -/
private theorem exists_isGenericPoint_of_mem_componentsOf {Y : Scheme.{u}} {D C : Set Y}
    (hD : IsClosed D) (hC : C ∈ componentsOf D) : ∃ ζ, IsGenericPoint ζ C := by
  have h := hC.1.1.isGenericPoint_genericPoint_closure
  rw [(Aux.isClosed_of_mem_componentsOf hD hC).closure_eq] at h
  exact ⟨_, h⟩

/-- A point of the biregular locus of `h` lies in the image of `h`. -/
private theorem exists_eq_of_mem_biregularLocus {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) {y : Y}
    (hy : y ∈ biregularLocus h) : ∃ x, h x = y := by
  set V := biregularLocus h
  have : IsIso (h ∣_ V) := isBiregular_biregularLocus h
  obtain ⟨p, hp⟩ := (asIso (h ∣_ V)).hom.homeomorph.surjective ⟨y, hy⟩
  refine ⟨(h ⁻¹ᵁ V).ι p, ?_⟩
  have e : V.ι ((h ∣_ V) p) = h ((h ⁻¹ᵁ V).ι p) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  rw [← e]
  exact congrArg Subtype.val hp

/-- `h` maps a birational transform `h⁻¹_* A` into `A`. -/
private theorem map_mem_of_inverseTransform {Y Y' : Scheme.{u}} {h : Y' ⟶ Y}
    {A : MMP.Mori.PrimeDivisor Y} {A' : MMP.Mori.PrimeDivisor Y'}
    (hA : inverseTransformPrimeDivisor h A = some A') {x : Y'}
    (hx : x ∈ (A'.support : Set Y')) : h x ∈ (A.support : Set Y) := by
  rw [mem_support_iff_specializes] at hx ⊢
  have := h.base.hom.map_specializes hx
  rwa [(MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hA).1] at this

/-- Over the biregular locus of `h`, the preimage of `A` lies in `h⁻¹_* A`. -/
private theorem mem_of_inverseTransform {Y Y' : Scheme.{u}} {h : Y' ⟶ Y}
    {A : MMP.Mori.PrimeDivisor Y} {A' : MMP.Mori.PrimeDivisor Y'}
    (hA : inverseTransformPrimeDivisor h A = some A') {x : Y'}
    (hx : h x ∈ (A.support : Set Y)) (hxV : h x ∈ biregularLocus h) :
    x ∈ (A'.support : Set Y') := by
  obtain ⟨h1, h2⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hA
  rw [mem_support_iff_specializes] at hx ⊢
  exact MMP.Threefold.Resolution.specializes_of_mem_biregularLocus h h2 hxV (h1 ▸ hx)

/-- A component of `D` whose generic point specializes a point `ξ` with `closure {ξ} ⊆ D` is
`closure {ξ}`. -/
private theorem eq_closure_of_specializes {T : Type*} [TopologicalSpace T] {D C : Set T} {ξ ζ : T}
    (hsub : closure {ξ} ⊆ D) (hC : C ∈ componentsOf D) (hζ : IsGenericPoint ζ C)
    (hξζ : ξ ⤳ ζ) : C = closure {ξ} := by
  have hle : C ⊆ closure {ξ} := by
    rw [← hζ.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξζ))
      isClosed_closure
  exact le_antisymm hle (hC.2 ⟨isIrreducible_singleton.closure, hsub⟩ hle)

/-- **The components of an intersection of transforms lie over the old ones.** Let
`h : Y' ⟶ Y` be an isomorphism over the complement of a closed set `W` with
`h⁻¹(W) = E`, and let `A' = h⁻¹_* A`, `B' = h⁻¹_* B`. If no irreducible component of `A' ∩ B'`
has its generic point on `E`, then `A' ∩ B'` has at most as many irreducible components as
`A ∩ B`, and strictly fewer when `W` is one of the components of `A ∩ B`. -/
private theorem ncard_componentsOf_inter_le {Y Y' : Scheme.{u}} [NoetherianSpace Y]
    (h : Y' ⟶ Y) {W : Set Y} (hWcl : IsClosed W) {E : Set Y'} (hE : E = h ⁻¹' W)
    (hV : ∀ y ∉ W, y ∈ biregularLocus h) {A B : MMP.Mori.PrimeDivisor Y}
    {A' B' : MMP.Mori.PrimeDivisor Y'} (hA : inverseTransformPrimeDivisor h A = some A')
    (hB : inverseTransformPrimeDivisor h B = some B')
    (hgen : ∀ C ∈ componentsOf ((A'.support : Set Y') ∩ B'.support), ∀ ζ, IsGenericPoint ζ C →
      ζ ∉ E) :
    (componentsOf ((A'.support : Set Y') ∩ B'.support)).ncard ≤
      (componentsOf ((A.support : Set Y) ∩ B.support)).ncard ∧
    (W ∈ componentsOf ((A.support : Set Y) ∩ B.support) →
      (componentsOf ((A'.support : Set Y') ∩ B'.support)).ncard <
        (componentsOf ((A.support : Set Y) ∩ B.support)).ncard) := by
  have hcl : IsClosed ((A.support : Set Y) ∩ B.support) :=
    A.idealSheaf.support.isClosed.inter B.idealSheaf.support.isClosed
  have hcl' : IsClosed ((A'.support : Set Y') ∩ B'.support) :=
    A'.idealSheaf.support.isClosed.inter B'.idealSheaf.support.isClosed
  have hfin := finite_componentsOf hcl
  let R : Set Y' → Set Y → Prop := fun C K => ∃ ζ, IsGenericPoint ζ C ∧ h ζ ∈ K
  have hex : ∀ C ∈ componentsOf ((A'.support : Set Y') ∩ B'.support),
      ∃ K ∈ componentsOf ((A.support : Set Y) ∩ B.support), R C K := by
    intro C hC
    obtain ⟨ζ, hζ⟩ := exists_isGenericPoint_of_mem_componentsOf hcl' hC
    have hζC : ζ ∈ (A'.support : Set Y') ∩ B'.support := hC.1.2 hζ.mem
    obtain ⟨K, hK, hζK⟩ := exists_mem_componentsOf (D := (A.support : Set Y) ∩ B.support)
      ⟨map_mem_of_inverseTransform hA hζC.1, map_mem_of_inverseTransform hB hζC.2⟩
    exact ⟨K, hK, ζ, hζ, hζK⟩
  have huniq : ∀ C ∈ componentsOf ((A'.support : Set Y') ∩ B'.support),
      ∀ C' ∈ componentsOf ((A'.support : Set Y') ∩ B'.support),
      ∀ K ∈ componentsOf ((A.support : Set Y) ∩ B.support), R C K → R C' K → C = C' := by
    intro C hC C' hC' K hK ⟨ζ, hζ, hζK⟩ ⟨ζ', hζ', hζ'K⟩
    obtain ⟨κ, hκ⟩ := exists_isGenericPoint_of_mem_componentsOf hcl hK
    have hκA : κ ∈ (A.support : Set Y) ∩ B.support := hK.1.2 hκ.mem
    have hζW : h ζ ∉ W := fun hw => hgen C hC ζ hζ (hE ▸ hw)
    have hζ'W : h ζ' ∉ W := fun hw => hgen C' hC' ζ' hζ' (hE ▸ hw)
    have hκζ : κ ⤳ h ζ := hκ.specializes hζK
    have hκζ' : κ ⤳ h ζ' := hκ.specializes hζ'K
    have hκW : κ ∉ W := fun hw => hζW (hκζ.mem_closed hWcl hw)
    obtain ⟨ξ, hξ⟩ := exists_eq_of_mem_biregularLocus h (hV κ hκW)
    have hξV : h ξ ∈ biregularLocus h := hξ ▸ hV κ hκW
    have hξζ : ξ ⤳ ζ := MMP.Threefold.Resolution.specializes_of_mem_biregularLocus h hξV
      (hV _ hζW) (hξ ▸ hκζ)
    have hξζ' : ξ ⤳ ζ' := MMP.Threefold.Resolution.specializes_of_mem_biregularLocus h hξV
      (hV _ hζ'W) (hξ ▸ hκζ')
    have hξAB : ξ ∈ (A'.support : Set Y') ∩ B'.support :=
      ⟨mem_of_inverseTransform hA (hξ ▸ hκA.1) hξV, mem_of_inverseTransform hB (hξ ▸ hκA.2) hξV⟩
    have hsub : closure {ξ} ⊆ (A'.support : Set Y') ∩ B'.support :=
      closure_minimal (Set.singleton_subset_iff.mpr hξAB) hcl'
    rw [eq_closure_of_specializes hsub hC hζ hξζ, eq_closure_of_specializes hsub hC' hζ' hξζ']
  refine ⟨ncard_le_of_rel hfin R hex huniq, fun hW => ncard_lt_of_rel hfin R hex huniq hW ?_⟩
  rintro C hC ⟨ζ, hζ, hζW⟩
  exact hgen C hC ζ hζ (hE ▸ hζW)

/-- The generic point of a closed irreducible set of codimension `n` has coheight `n`. -/
private theorem coheight_eq_of_isGenericPoint {Y : Scheme.{u}} {ζ : Y} {C : Set Y}
    (hζ : IsGenericPoint ζ C) {n : ℕ} (h : closedsCodimension (Closeds.closure C) = n) :
    Order.coheight ζ = n := by
  rw [← MMP.Flips.codimension_closureSingleton, ← closedsCodimension_coe, ← h]
  congr 1
  ext1
  rw [Closeds.coe_closure, ← hζ.def, closure_closure]
  rfl

/-- Distinct prime divisors have distinct birational transforms. -/
private theorem inverseTransformPrimeDivisor_ne {X Y : Scheme.{u}} {f : Y ⟶ X}
    {D D' : MMP.Mori.PrimeDivisor X} {E E' : MMP.Mori.PrimeDivisor Y}
    (hE : inverseTransformPrimeDivisor f D = some E)
    (hE' : inverseTransformPrimeDivisor f D' = some E') (hD : D ≠ D') : E ≠ E' := by
  rintro rfl
  exact hD <| AlgebraicGeometry.PrimeDivisor.genericPoint_injective <| Eq.trans
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE).1.symm
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1

/-- **The exceptional set of a blow-up-like morphism.** If `h : Y' ⟶ Y` is an isomorphism off
`W`, the preimage `h⁻¹(W)` is a prime divisor `E`, and the generic point of `E` maps to a point
of coheight two, then `Ex(h) = E`. -/
private theorem coe_exceptionalSet_eq_support {Y Y' : Scheme.{u}} (h : Y' ⟶ Y) {W : Set Y}
    {E : MMP.Mori.PrimeDivisor Y'} (hE : (E.support : Set Y') = h ⁻¹' W)
    (hV : ∀ y ∉ W, y ∈ biregularLocus h) (hcoh : Order.coheight (h E.genericPoint) = 2) :
    (exceptionalSet h : Set Y') = E.support := by
  refine subset_antisymm (fun y hy => hE ▸ not_not.mp fun hyW => hy (hV _ hyW)) fun y hy => ?_
  have hεEx : E.genericPoint ∈ (exceptionalSet h : Set Y') := fun hεV => by
    have := MMP.Positivity.coheight_map_of_mem_biregularLocus h hεV
    rw [hcoh, E.coheight_genericPoint] at this
    exact absurd this (by decide)
  exact ((mem_support_iff_specializes E).mp hy).mem_closed (exceptionalSet h).isClosed hεEx

/-- **No codimension-two stratum lies in a third component.** Let `∑_{F ∈ s} F` be an snc
divisor on a smooth variety and `A`, `B`, `E` three distinct members of `s`. Then the generic
point of an irreducible component of `A ∩ B`, which has codimension two, does not lie on `E`:
at a point of `A ∩ B ∩ E` the local ring has dimension at least three. -/
private theorem genericPoint_notMem_of_isSNC {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY)
    (hsm : IsSmoothScheme sY) (s : Finset (MMP.Mori.PrimeDivisor Y))
    (hsnc : DivisorWithCoeffs.IsSNC sY (∑ F ∈ s, Finsupp.single F (1 : ℤ)))
    {A B E : MMP.Mori.PrimeDivisor Y} (hA : A ∈ s) (hB : B ∈ s) (hE : E ∈ s)
    (hAB : A ≠ B) (hAE : A ≠ E) (hBE : B ≠ E)
    {C : Set Y} (hC : C ∈ componentsOf ((A.support : Set Y) ∩ B.support)) {ζ : Y}
    (hζ : IsGenericPoint ζ C) : ζ ∉ (E.support : Set Y) := by
  classical
  intro hζE
  let S : s → MMP.Mori.PrimeDivisor Y := Subtype.val
  have hSNC : DivisorWithCoeffs.IsSNC sY (∑ j, Finsupp.single (S j) (1 : ℤ)) := by
    rwa [Finset.sum_coe_sort s (fun P => Finsupp.single P (1 : ℤ))]
  let ja : s := ⟨A, hA⟩
  let jb : s := ⟨B, hB⟩
  let J : Finset s := {ja, jb}
  have hjab : ja ≠ jb := fun h => hAB (congrArg Subtype.val h)
  have hJ : J.card = 2 := Finset.card_pair hjab
  have hinter : (⋂ j ∈ J, ((S j).support : Set Y)) = (A.support : Set Y) ∩ B.support := by
    simp [J, S, ja, jb]
  obtain ⟨-, hcodim, -⟩ := blowUp_snc_stratum sY hY hsm S Subtype.val_injective hSNC J hJ.ge
    ⟨C, hinter ▸ hC⟩
  have hcoh : Order.coheight ζ = 2 := coheight_eq_of_isGenericPoint hζ (by rw [hcodim, hJ])
  obtain ⟨n, z, j, hz, hj, -⟩ := hsnc.2 ζ
  have hn : n = 2 := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight, hcoh] at h
    exact_mod_cast h.symm
  have hζAB : ζ ∈ (A.support : Set Y) ∩ B.support := hC.1.2 hζ.mem
  let a : {F : MMP.Mori.PrimeDivisor Y //
    F ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ ζ ∈ F.support} :=
    ⟨A, mem_support_sum_single hA, hζAB.1⟩
  let b : {F : MMP.Mori.PrimeDivisor Y //
    F ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ ζ ∈ F.support} :=
    ⟨B, mem_support_sum_single hB, hζAB.2⟩
  let e : {F : MMP.Mori.PrimeDivisor Y //
    F ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ ζ ∈ F.support} :=
    ⟨E, mem_support_sum_single hE, hζE⟩
  have h1 := (j a).isLt
  have h2 := (j b).isLt
  have h3 := (j e).isLt
  have hab := Fin.val_ne_of_ne (show j a ≠ j b from fun h => hAB (congrArg Subtype.val (hj h)))
  have hae := Fin.val_ne_of_ne (show j a ≠ j e from fun h => hAE (congrArg Subtype.val (hj h)))
  have hbe := Fin.val_ne_of_ne (show j b ≠ j e from fun h => hBE (congrArg Subtype.val (hj h)))
  omega

/-- The inductive invariant: `f` is a log resolution of `(X, Δ)` from a variety, and every
component of `Δ` has a birational transform under `f`. -/
private def Good {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (Δ : QDivisor X) (f : Y ⟶ X) : Prop :=
  IsLogResolution sX (QDivisor.toRDivisor Δ) f ∧ MMP.Mori.IsVariety k (f ≫ sX) ∧
    ∀ D ∈ Δ.support, ∃ E, inverseTransformPrimeDivisor f D = some E

private theorem exists_good {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X]
    (Δ : QDivisor X) (hΔ : IsPair sX Δ) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Good sX Δ f := by
  have hX := hΔ.isNormalVariety
  obtain ⟨Y, g, hg⟩ := exists_isLogResolution sX hX (QDivisor.toRDivisor Δ)
  have hYv : MMP.Mori.IsVariety k (g ≫ sX) :=
    (hg.toIsSmoothResolution.isNormalVariety hX).1.1
  have : IsProper g := hg.isProper
  have := hX.1
  refine ⟨Y, g, hg, hYv, fun D _ => ?_⟩
  have hV : D.genericPoint ∈ biregularLocus g := by
    by_contra hV
    have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
      (two_le_closedsCodimension_compl_biregularLocus sX g hg.isBirationalMorphism)
      D.genericPoint hV
    rw [D.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨E, hE, -⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some D hV
  exact ⟨E, hE⟩

/-- If `f` is an isomorphism over `V` and `h` an isomorphism over `f⁻¹(V)`, then `h ≫ f` is an
isomorphism over `V`. -/
private theorem isBiregular_comp {X Y Y' : Scheme.{u}} {f : Y ⟶ X} {h : Y' ⟶ Y} {V : X.Opens}
    (hf : V ≤ biregularLocus f) (hh : f ⁻¹ᵁ V ≤ biregularLocus h) : IsBiregular (h ≫ f) V := by
  unfold IsBiregular
  rw [morphismRestrict_comp]
  have h1 : IsIso (f ∣_ V) := isBiregular_iff_le_biregularLocus.mpr hf
  have h2 : IsIso (h ∣_ f ⁻¹ᵁ V) := isBiregular_iff_le_biregularLocus.mpr hh
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h1

/-- Let `h` be an isomorphism off a component `W` of `E₁ ∩ E₂`, for distinct prime divisors
`E₁, E₂`. If `A = f⁻¹_* D` and `A' = h⁻¹_* A`, then `A' = (h ≫ f)⁻¹_* D`. -/
private theorem inverseTransformPrimeDivisor_comp_eq_some {X Y Y' : Scheme.{u}} {f : Y ⟶ X}
    [IsProper f] {h : Y' ⟶ Y} {W : Set Y} (hWcl : IsClosed W) {E₁ E₂ : MMP.Mori.PrimeDivisor Y}
    (hE₁₂ : E₁ ≠ E₂) (hW : W ∈ componentsOf ((E₁.support : Set Y) ∩ E₂.support))
    (hV : ∀ y ∉ W, y ∈ biregularLocus h) {D : MMP.Mori.PrimeDivisor X}
    {A : MMP.Mori.PrimeDivisor Y} (hA : inverseTransformPrimeDivisor f D = some A)
    {A' : MMP.Mori.PrimeDivisor Y'} (hA' : inverseTransformPrimeDivisor h A = some A') :
    inverseTransformPrimeDivisor (h ≫ f) D = some A' := by
  obtain ⟨hηA, hAV⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hA
  let V : X.Opens := biregularLocus f ⊓ ⟨(f '' W)ᶜ, (f.isClosedMap W hWcl).isOpen_compl⟩
  have hVbir : IsBiregular (h ≫ f) V :=
    isBiregular_comp inf_le_left fun y hy => hV y fun hyW => hy.2 ⟨y, hyW, rfl⟩
  have hηD : D.genericPoint ∈ V := by
    refine ⟨hηA ▸ hAV, ?_⟩
    rintro ⟨w, hwW, hw⟩
    have hwV : f w ∈ biregularLocus f := hw ▸ hηA ▸ hAV
    have hw' : f w = f A.genericPoint := hw.trans hηA.symm
    have hwA : w = A.genericPoint := Inseparable.eq <|
      (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f hwV hAV
        (hw' ▸ le_rfl)).antisymm
      (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f hAV hwV (hw' ▸ le_rfl))
    have hAW := hW.1.2 (hwA ▸ hwW)
    exact hE₁₂ (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((E₁.eq_genericPoint_of_mem_support hAW.1 A.coheight_genericPoint).symm.trans
        (E₂.eq_genericPoint_of_mem_support hAW.2 A.coheight_genericPoint)))
  have hη : (h ≫ f) A'.genericPoint = D.genericPoint := by
    rw [Scheme.Hom.comp_apply,
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hA').1,
      hηA]
  exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη
    (hη ▸ le_biregularLocus hVbir hηD)

/-- Let `h` be an isomorphism off `W` with exceptional set `E = h⁻¹(W)`, and let `S'` send each
member of `s` to its transform under `h`. Then the components of `{E} ∪ S'(s)` cover
`Ex(h) ∪ h⁻¹(Supp Δ)` whenever `Supp Δ` is the union of the members of `s`. -/
private theorem iUnion_insert_image_eq {Y Y' : Scheme.{u}} {h : Y' ⟶ Y} {W : Set Y}
    {E : MMP.Mori.PrimeDivisor Y'} (hExh : (exceptionalSet h : Set Y') = E.support)
    (hE : (E.support : Set Y') = h ⁻¹' W) (hV : ∀ y ∉ W, y ∈ biregularLocus h)
    {s : Finset (MMP.Mori.PrimeDivisor Y)} {Δ : RDivisor Y}
    (hΔ : (Δ.supp : Set Y) = ⋃ T ∈ s, (T.support : Set Y)) {S' : s → MMP.Mori.PrimeDivisor Y'}
    (hS'tr : ∀ j : s, inverseTransformPrimeDivisor h j.1 = some (S' j))
    [DecidableEq (MMP.Mori.PrimeDivisor Y')] :
    (⋃ F ∈ insert E (Finset.univ.image S'), (F.support : Set Y')) =
      ↑(exceptionalSet h ⊔ Δ.supp.preimage h.continuous) := by
  ext y
  rw [Set.mem_iUnion₂]
  change _ ↔ y ∈ (exceptionalSet h : Set Y') ∨ h y ∈ (Δ.supp : Set Y)
  rw [hExh, hΔ]
  constructor
  · rintro ⟨F, hF, hyF⟩
    rcases Finset.mem_insert.mp hF with rfl | hF
    · exact Or.inl hyF
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hF
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨j.1, j.2, map_mem_of_inverseTransform (hS'tr j) hyF⟩)
  · rintro (hy | hy)
    · exact ⟨E, Finset.mem_insert_self _ _, hy⟩
    · obtain ⟨T, hT, hyT⟩ := Set.mem_iUnion₂.mp hy
      by_cases hyE : y ∈ (E.support : Set Y')
      · exact ⟨E, Finset.mem_insert_self _ _, hyE⟩
      · exact ⟨S' ⟨T, hT⟩, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)),
          mem_of_inverseTransform (hS'tr ⟨T, hT⟩) hyT (hV _ fun hw => hyE (hE ▸ hw))⟩

/-- **The measure drops along the blow-up.** Let `h` be an isomorphism off a component `W` of
`f⁻¹_* D₁ ∩ f⁻¹_* D₂`, with exceptional divisor `E = h⁻¹(W)`, such that the transforms under
`h ≫ f` of the components of `𝒟` are the transforms under `h` of their transforms under `f`, and
these together with `E` form an snc divisor. Then `h ≫ f` has smaller measure than `f`. -/
private theorem measure_comp_lt {k : Type u} [Field k] [PerfectField k] {X Y Y' : Scheme.{u}}
    [NoetherianSpace Y] {sX : X ⟶ Spec (.of k)} {𝒟 : Finset (MMP.Mori.PrimeDivisor X)}
    {f : Y ⟶ X} (h : Y' ⟶ Y) (hY'v : MMP.Mori.IsVariety k (h ≫ f ≫ sX))
    (hsm : IsSmoothScheme (h ≫ f ≫ sX)) {W : Set Y} (hWcl : IsClosed W)
    {E : MMP.Mori.PrimeDivisor Y'} (hE : (E.support : Set Y') = h ⁻¹' W)
    (hV : ∀ y ∉ W, y ∈ biregularLocus h)
    (hτ : ∀ D ∈ 𝒟, ∃ A, inverseTransformPrimeDivisor f D = some A)
    {s : Finset (MMP.Mori.PrimeDivisor Y)}
    (hs : ∀ D ∈ 𝒟, ∀ A, inverseTransformPrimeDivisor f D = some A → A ∈ s)
    {S' : s → MMP.Mori.PrimeDivisor Y'}
    (hS'tr : ∀ j : s, inverseTransformPrimeDivisor h j.1 = some (S' j))
    (hS'inj : Function.Injective S') (hS'E : ∀ j, S' j ≠ E)
    (htr : ∀ {D A A'}, inverseTransformPrimeDivisor f D = some A →
      inverseTransformPrimeDivisor h A = some A' → inverseTransformPrimeDivisor (h ≫ f) D = some A')
    {s' : Finset (MMP.Mori.PrimeDivisor Y')}
    (hsnc : DivisorWithCoeffs.IsSNC (h ≫ f ≫ sX) (∑ F ∈ s', Finsupp.single F (1 : ℤ)))
    (hS's : ∀ j, S' j ∈ s') (hEs' : E ∈ s') {D₁ D₂ : MMP.Mori.PrimeDivisor X}
    (hp : (D₁, D₂) ∈ 𝒟.offDiag) {E₁ E₂ : MMP.Mori.PrimeDivisor Y}
    (hE₁ : inverseTransformPrimeDivisor f D₁ = some E₁)
    (hE₂ : inverseTransformPrimeDivisor f D₂ = some E₂)
    (hW : W ∈ componentsOf ((E₁.support : Set Y) ∩ E₂.support)) :
    measure 𝒟 (h ≫ f) < measure 𝒟 f := by
  have hpair : ∀ p ∈ 𝒟.offDiag,
      (componentsOf (tsupp (h ≫ f) p.1 ∩ tsupp (h ≫ f) p.2)).ncard ≤
        (componentsOf (tsupp f p.1 ∩ tsupp f p.2)).ncard ∧
      (p = (D₁, D₂) → (componentsOf (tsupp (h ≫ f) p.1 ∩ tsupp (h ≫ f) p.2)).ncard <
        (componentsOf (tsupp f p.1 ∩ tsupp f p.2)).ncard) := by
    rintro ⟨Da, Db⟩ hpab
    obtain ⟨hDa, hDb, hDab⟩ := Finset.mem_offDiag.mp hpab
    obtain ⟨A, hA⟩ := hτ Da hDa
    obtain ⟨B, hB⟩ := hτ Db hDb
    have hAs := hs Da hDa A hA
    have hBs := hs Db hDb B hB
    have hAB : A ≠ B := inverseTransformPrimeDivisor_ne hA hB hDab
    simp only [tsupp_eq hA, tsupp_eq hB, tsupp_eq (htr hA (hS'tr ⟨A, hAs⟩)),
      tsupp_eq (htr hB (hS'tr ⟨B, hBs⟩))]
    have hneq : S' ⟨A, hAs⟩ ≠ S' ⟨B, hBs⟩ := fun e => hAB (congrArg Subtype.val (hS'inj e))
    obtain ⟨hle, hlt⟩ := ncard_componentsOf_inter_le h hWcl hE hV (hS'tr ⟨A, hAs⟩)
      (hS'tr ⟨B, hBs⟩) (fun C hC ζ hζ => genericPoint_notMem_of_isSNC (h ≫ f ≫ sX) hY'v hsm s'
        hsnc (hS's _) (hS's _) hEs' hneq (hS'E _) (hS'E _) hC hζ)
    refine ⟨hle, fun hp => ?_⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    obtain rfl : A = E₁ := Option.some_injective _ (hA.symm.trans hE₁)
    obtain rfl : B = E₂ := Option.some_injective _ (hB.symm.trans hE₂)
    exact hlt hW
  unfold measure
  exact Finset.sum_lt_sum (fun p hp => (hpair p hp).1) ⟨(D₁, D₂), hp, (hpair _ hp).2 rfl⟩

/-- The support of `∑_{T ∈ s} T` is the union of the members of `s`. -/
private theorem coe_supp_sum_single {Y : Scheme.{u}} (s : Finset (MMP.Mori.PrimeDivisor Y)) :
    ((∑ T ∈ s, Finsupp.single T (1 : ℝ) : RDivisor Y).supp : Set Y) =
      ⋃ T ∈ s, (T.support : Set Y) := by
  classical
  have : (∑ T ∈ s, Finsupp.single T (1 : ℝ) : RDivisor Y).support = s := by
    ext F
    simp [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [DivisorWithCoeffs.coe_supp, this]

/-- A closed set whose underlying set is a prime divisor is of pure codimension one. -/
private theorem isPureCodimOne_of_coe_eq_support {Y : Scheme.{u}} {Z : Closeds Y}
    {E : MMP.Mori.PrimeDivisor Y} (hZ : (Z : Set Y) = E.support) : IsPureCodimOne Z := by
  intro W' hW'
  let EI := IrreducibleCloseds.closureSingleton E.genericPoint
  have hEI : (EI : Set Y) = E.support := (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have h1 : (W' : Set Y) ⊆ E.support := hZ ▸ hW'.1
  have h2 : W' ≤ EI := fun x hx => by
    rw [← SetLike.mem_coe, hEI]
    exact h1 hx
  rw [le_antisymm h2 (hW'.2 (show (EI : Set Y) ⊆ Z by rw [hEI, ← hZ]) h2)]
  exact E.codimension_one

private theorem exists_good_measure_lt {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (Δ : QDivisor X) {Y : Scheme.{u}} (f : Y ⟶ X) (hf : Good sX Δ f)
    (hpos : 0 < measure Δ.support f) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X), Good sX Δ f' ∧
      measure Δ.support f' < measure Δ.support f := by
  classical
  obtain ⟨hfl, hYv, hτ⟩ := hf
  have := noetherianSpace_of_isVariety hYv
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsProper f := hfl.isProper
  obtain ⟨⟨D₁, D₂⟩, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  obtain ⟨hD₁, hD₂, hD₁₂⟩ := Finset.mem_offDiag.mp hp
  obtain ⟨E₁, hE₁⟩ := hτ D₁ hD₁
  obtain ⟨E₂, hE₂⟩ := hτ D₂ hD₂
  simp only [tsupp_eq hE₁, tsupp_eq hE₂] at hne
  obtain ⟨W, hW⟩ := Set.nonempty_of_ncard_ne_zero hne
  obtain ⟨s, hs, hsnc, hE₁s⟩ := exists_snc_family hfl hD₁ hE₁
  have hE₂s := mem_of_iUnion_eq hs hD₂ hE₂
  have hE₁₂ : E₁ ≠ E₂ := inverseTransformPrimeDivisor_ne hE₁ hE₂ hD₁₂
  have hcl₁₂ : IsClosed ((E₁.support : Set Y) ∩ E₂.support) :=
    E₁.idealSheaf.support.isClosed.inter E₂.idealSheaf.support.isClosed
  have hWcl : IsClosed W := Aux.isClosed_of_mem_componentsOf hcl₁₂ hW
  let S : s → MMP.Mori.PrimeDivisor Y := Subtype.val
  have hSNC : DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ j, Finsupp.single (S j) (1 : ℤ)) := by
    rwa [Finset.sum_coe_sort s (fun P => Finsupp.single P (1 : ℤ))]
  let j₁ : s := ⟨E₁, hE₁s⟩
  let j₂ : s := ⟨E₂, hE₂s⟩
  let J : Finset s := {j₁, j₂}
  have hj₁₂ : j₁ ≠ j₂ := fun h => hE₁₂ (congrArg Subtype.val h)
  have hJ : J.card = 2 := Finset.card_pair hj₁₂
  have hinter : (⋂ j ∈ J, ((S j).support : Set Y)) = (E₁.support : Set Y) ∩ E₂.support := by
    simp [J, S, j₁, j₂]
  let Wc : componentsOf (⋂ j ∈ J, ((S j).support : Set Y)) := ⟨W, hinter ▸ hW⟩
  have key := blowUp_snc_stratum (f ≫ sX) hYv hfl.isSmoothScheme S Subtype.val_injective hSNC J
    hJ.ge Wc
  dsimp only at key
  have hIsupp : ((componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) Wc).support : Set Y) =
      W := by
    change ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure W)).support : Set Y) = W
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, hWcl.closure_eq]
  generalize componentsFamily (⋂ j ∈ J, ((S j).support : Set Y)) Wc = I at key hIsupp
  obtain ⟨-, hcodim, hBsm, hiso, E, S', hEI, -, hS'tr, hS'inj, hS'E, hsnc', himg, -⟩ := key
  set h := blowUpToBase I with hhdef
  have hEsupp : (E.support : Set (blowUp I)) = h ⁻¹' W := by
    rw [← hIsupp]
    change ((E.idealSheaf).support : Set (blowUp I)) = _
    rw [hEI, Scheme.IdealSheafData.support_comap]
    rfl
  have hVh : ∀ y ∉ W, y ∈ biregularLocus h := fun y hy =>
    le_biregularLocus hiso (show y ∉ (I.support : Set Y) by rwa [hIsupp])
  have hirr : IsIrreducible (I.support : Set Y) := hIsupp ▸ hW.1.1
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
    have e : (⟨((⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) : Set Y),
        (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y).isClosed⟩ : Closeds Y) =
        Closeds.closure W := by
      ext1
      exact hIsupp.trans hWcl.closure_eq.symm
    rw [← closedsCodimension_coe, e, hcodim, hJ]
    norm_num
  have : IsIntegral (blowUp I) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have hbir : IsBirationalMorphism h :=
    MMP.Threefold.Resolution.isBirationalMorphism_blowUpToBase I hirr hc1
  have hI0 := MMP.Threefold.Resolution.ne_bot_of_one_le_codimension I hirr hc1
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hYv
  obtain ⟨hY'v, hproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational (f ≫ sX) I hI0
  have : IsProper h := hproj.isProper
  have hj₁J : j₁ ∈ J := by simp [J]
  have hεW : closure {h E.genericPoint} = W := by
    apply subset_antisymm
    · refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hWcl
      simpa [hEsupp] using MMP.Flips.primeDivisor_genericPoint_mem_support E
    · intro w hw
      have hw' : w ∈ (Wc : Set Y) := hw
      rw [← himg j₁ hj₁J] at hw'
      obtain ⟨y, ⟨-, hy⟩, rfl⟩ := hw'
      exact specializes_iff_mem_closure.mp
        (h.base.hom.map_specializes ((mem_support_iff_specializes E).mp hy))
  have hcohε : Order.coheight (h E.genericPoint) = 2 :=
    coheight_eq_of_isGenericPoint hεW (by rw [hcodim, hJ])
  have hExh : (exceptionalSet h : Set (blowUp I)) = E.support :=
    coe_exceptionalSet_eq_support h hEsupp hVh hcohε
  let Δ' : RDivisor Y := ∑ T ∈ s, Finsupp.single T (1 : ℝ)
  have hsuppΔ' : (Δ'.supp : Set Y) = ⋃ T ∈ s, (T.support : Set Y) := coe_supp_sum_single s
  let s' : Finset (MMP.Mori.PrimeDivisor (blowUp I)) := insert E (Finset.univ.image S')
  have hEimg : E ∉ Finset.univ.image S' := by
    simpa using hS'E
  have hS's : ∀ j, S' j ∈ s' := fun j =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hEs' : E ∈ s' := Finset.mem_insert_self _ _
  have hsnc's : DivisorWithCoeffs.IsSNC (h ≫ f ≫ sX)
      (∑ F ∈ s', Finsupp.single F (1 : ℤ)) := by
    rwa [Finset.sum_insert hEimg, Finset.sum_image fun i _ j _ h => hS'inj h]
  have hunion : (⋃ F ∈ s', (F.support : Set (blowUp I))) =
      ↑(exceptionalSet h ⊔ Δ'.supp.preimage h.continuous) :=
    iUnion_insert_image_eq hExh hEsupp hVh hsuppΔ' hS'tr
  have hlogh : IsLogResolution (f ≫ sX) Δ' h :=
    ⟨⟨inferInstance, hbir, hBsm⟩, isPureCodimOne_of_coe_eq_support hExh,
      Or.inr ⟨s', hunion, hsnc's⟩⟩
  have hΔ'le : exceptionalSet f ⊔ (QDivisor.toRDivisor Δ).supp.preimage f.continuous ≤
      Δ'.supp := by
    intro y hy
    rw [← SetLike.mem_coe, hsuppΔ', hs]
    exact hy
  have htr : ∀ {D A A'}, inverseTransformPrimeDivisor f D = some A →
      inverseTransformPrimeDivisor h A = some A' →
        inverseTransformPrimeDivisor (h ≫ f) D = some A' :=
    fun hA hA' => inverseTransformPrimeDivisor_comp_eq_some hWcl hE₁₂ hW hVh hA hA'
  refine ⟨blowUp I, h ≫ f, ⟨hfl.comp hΔ'le hlogh, by rwa [Category.assoc], fun D hD => ?_⟩,
    measure_comp_lt h hY'v hBsm hWcl hEsupp hVh hτ (fun D hD A hA => mem_of_iUnion_eq hs hD hA)
      hS'tr hS'inj hS'E htr hsnc's hS's hEs' hp hE₁ hE₂ hW⟩
  obtain ⟨A, hA⟩ := hτ D hD
  exact ⟨_, htr hA (hS'tr ⟨A, mem_of_iUnion_eq hs hD hA⟩)⟩

/-- Every model satisfying `Good` can be replaced by one satisfying `Good` of measure `0`. -/
private theorem exists_good_measure_eq_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (Δ : QDivisor X) {Y : Scheme.{u}} (f : Y ⟶ X) (hf : Good sX Δ f) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X), Good sX Δ f' ∧ measure Δ.support f' = 0 := by
  induction hn : measure Δ.support f using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨Y, f, hf, hn⟩
    · obtain ⟨Y', f', hf', hlt⟩ := exists_good_measure_lt sX Δ f hf (hn ▸ hpos)
      exact ih _ (hn ▸ hlt) f' hf' rfl

end Proof_lem_km2b_log_resolution_disjoint_boundary_transforms

namespace MMP.Mori

open CategoryTheory TopologicalSpace MMP.Resolution
open AlgebraicGeometry hiding PrimeDivisor
open Proof_lem_km2b_log_resolution_disjoint_boundary_transforms

/-- Let `(X, Δ)` be a pair over an algebraically closed field `k` of characteristic zero. Then
there is a log resolution `f : Y ⟶ X` of `(X, Δ)` such that the birational transforms
`f⁻¹_* D` of the components `D` of `Δ` are smooth over `k` and pairwise disjoint. -/
@[mmp "lem_km2b_log_resolution_disjoint_boundary_transforms"]
public theorem exists_isLogResolution_disjoint_inverseTransformPrimeDivisor {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] (Δ : QDivisor X) (hΔ : IsPair sX Δ) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsLogResolution sX (QDivisor.toRDivisor Δ) f ∧
      (∀ D ∈ Δ.support, ∀ E : PrimeDivisor Y, inverseTransformPrimeDivisor f D = some E →
        IsSmoothScheme (E.idealSheaf.subschemeι ≫ f ≫ sX)) ∧
      ∀ D ∈ Δ.support, ∀ D' ∈ Δ.support, D ≠ D' → ∀ E E' : PrimeDivisor Y,
        inverseTransformPrimeDivisor f D = some E → inverseTransformPrimeDivisor f D' = some E' →
          Disjoint (E.support : Set Y) E'.support := by
  classical
  obtain ⟨Y₀, g, hg⟩ := exists_good sX Δ hΔ
  obtain ⟨Y, f, ⟨hf, hYv, -⟩, h0⟩ := exists_good_measure_eq_zero sX Δ g hg
  have := noetherianSpace_of_isVariety hYv
  refine ⟨Y, f, hf, fun D hD E hE => ?_, fun D hD D' hD' hDD' E E' hE hE' => ?_⟩
  · obtain ⟨s, -, hsnc, hEs⟩ := exists_snc_family hf hD hE
    exact hsnc.1 E (mem_support_sum_single hEs)
  · have hterm := (Finset.sum_eq_zero_iff.mp h0) (D, D')
      (Finset.mem_offDiag.mpr ⟨hD, hD', hDD'⟩)
    simp only [tsupp_eq hE, tsupp_eq hE'] at hterm
    have hcl : IsClosed ((E.support : Set Y) ∩ E'.support) :=
      E.idealSheaf.support.isClosed.inter E'.idealSheaf.support.isClosed
    rw [Set.ncard_eq_zero (finite_componentsOf hcl)] at hterm
    rw [Set.disjoint_iff]
    intro x hx
    obtain ⟨W, hW, -⟩ := exists_mem_componentsOf hx
    simp [hterm] at hW

end MMP.Mori

namespace MMP.Mori

open CategoryTheory TopologicalSpace
open AlgebraicGeometry hiding PrimeDivisor

/-- **Criterion for dlt pairs** (Kollár–Mori, Proposition 2.40, corrected). Let `(X, Δ)` be a
pair, with canonical divisor `K` of dimension `n`, whose coefficients lie in `[0, 1]`. Then
`(X, Δ)` is dlt if and only if there is a closed subset `Z ≠ X` such that `X \ Z` is smooth,
`Δ|_{X \ Z}` is snc, and there is a log resolution `f : Y ⟶ X` of `(X, Δ)` such that `f⁻¹(Z)` is
empty or of pure codimension one, `Ex(f) ∪ f⁻¹(Supp Δ) ∪ f⁻¹(Z)` is an snc divisor, and
`a(E, X, Δ) > -1` for every prime divisor `E` of `Y` contained in `f⁻¹(Z)`. -/
@[mmp "prop_km2b_dlt_criterion_log_resolution"]
public theorem isDltPair_iff_exists_isLogResolution {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hΔ : IsPairWith sX n K Δ) (hcoeff : ∀ P : PrimeDivisor X, 0 ≤ Δ.coeff P ∧ Δ.coeff P ≤ 1) :
    IsDltPair sX n K Δ ↔
      ∃ Z : Closeds X, Z ≠ ⊤ ∧ (Z.compl : X.Opens) ≤ smoothLocus sX ∧
        (Δ.restrictOpen (Z.compl : X.Opens)).IsSNC (Scheme.Opens.ι (X := X) Z.compl ≫ sX) ∧
        ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f),
          IsPureCodimOne (Z.preimage f.continuous) ∧
          IsSNCSubset (f ≫ sX)
            (exceptionalSet f ⊔ Δ.supp.preimage f.continuous ⊔ Z.preimage f.continuous) ∧
          ∀ (hY : IsNormalVariety k (f ≫ sX)) (E : PrimeDivisor Y),
            E.support ⊆ f ⁻¹' (Z : Set X) → ∀ a : ℚ,
              IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf.isBirationalMorphism, E⟩ a →
                -1 < a := by
  constructor
  · intro h
    obtain ⟨U, hUne, hU, hUsnc, hdisc, -⟩ := MMP.Threefold.Mori.IsDltPair.exists_open_nonempty h
    let Z : Closeds X := U.compl
    have hZU : (Z.compl : X.Opens) = U := Opens.compl_compl U
    have hZ : Z ≠ ⊤ := by
      intro hZ
      obtain ⟨x, hx⟩ := hUne
      exact (show x ∈ (Z : Set X) by rw [hZ]; trivial) hx
    obtain ⟨Y, f, hf, hpure, hsnc⟩ := exists_isLogResolution_isPureCodimOne_preimage sX hΔ.1
      (QDivisor.toRDivisor Δ) Z hZ
    rw [QDivisor.supp_toRDivisor] at hsnc
    refine ⟨Z, hZ, hZU ▸ hU, hZU ▸ hUsnc, Y, f, hf, hpure, hsnc,
      fun hY E hE a ha => hdisc _ a ?_ ha⟩
    rw [DivisorOver.coe_center]
    exact closure_minimal (Set.image_subset_iff.mpr hE) Z.isClosed
  · rintro ⟨Z, hZ, hsm, hsnc, Y, f, hf, hpure, hS, hG⟩
    obtain ⟨δ, hδ, hb⟩ := exists_pos_forall_le_discrepancy_of_isLogResolution hΔ hcoeff hZ hsm
      hsnc hf hpure hS hG
    exact ⟨hΔ, hcoeff, Z.compl, hsm, hsnc, fun D a hD ha => by
      linarith [hb D a (by simpa using hD) ha]⟩

end MMP.Mori

end
