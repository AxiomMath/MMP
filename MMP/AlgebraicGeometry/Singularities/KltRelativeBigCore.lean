module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
public import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
public import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial

/-!
# An ample core for a polytope of boundaries containing a relatively big divisor

Let `f : Y ⟶ S` be a morphism of projective varieties over an algebraically closed field of
characteristic zero, with `Y` normal and `ℚ`-factorial, `G ≥ 0` an `f`-big `ℚ`-divisor and `V` a
finite set of klt boundaries `Γ ≥ G`. Writing `G ∼_ℚ H + E - f^*T` by the relative Kodaira
decomposition and choosing a small rational `ε = 1/N` such that every `(Y, Γ + ε(H + E))`,
`Γ ∈ V`, is klt (Kollár–Mori 2.35(2)), the divisors `A' = εH` and `T_Y = ε(H + E - G)` satisfy
`Γ + T_Y - A' = Γ - εG + εE ≥ 0` on the convex hull of `V`, and
`Γ + T_Y - A' ≤ Γ + T_Y ≤ Γ + ε(H + E)`, so both are klt by monotonicity.

Kollár–Mori 2.35(2) is proved here on the way: on a log resolution of `(X, Supp Δ ∪ Supp Δ')`,
the discrepancy of `(X, Δ + εΔ')` near `ε = 0` is a minimum of finitely many affine functions
of `ε`.

## Main results

* `MMP.Fourfold.QDivisor.IsRelativelyBig.exists_isKltPair_add_pullback_sub_isAmple`.

## Implementation notes

* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero, the setting of
  `MMP.Mori.QDivisor.IsRelativelyBig.exists_qLinearlyEquivalent_add_sub_pullback`.
* The rational polytope is the `ℚ`-convex hull of a finite set `V` of `ℚ`-divisors. Effectivity
  of its members and `G ≤ Γ` are convex conditions, so they are assumed at the points of `V`.
* "`T_Y` is `ℚ`-linearly equivalent to a pull-back from `S`" is `T_Y ∼_ℚ c • [T₀']` with
  `T₀'` a Cartier pull-back (`MMP.Intersection.IsPullback`) of a Cartier divisor `T₀` on `S`,
  `[T₀']` its Weil divisor (`MMP.Intersection.IsWeilDivisorOfCartier`) and `c ∈ ℚ`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.32, 2.35
-/

universe u

section

open CategoryTheory TopologicalSpace MMP.Mori MMP.Resolution Filter Topology
open AlgebraicGeometry hiding PrimeDivisor

namespace MMP.Mori.KltRelativeBigCore

/-! ### Snc closed subsets are snc divisors -/

/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : MMP.Mori.DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]
    exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
private theorem isSNCSubset_of_isSNCClosedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : MMP.Mori.PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      exists_primeDivisor_of_isSNCFamily hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rwa [hPs]
    · refine isSNC_of_isSNCFamily hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-! ### Existence of log resolutions -/

/-- **Log resolutions exist** in characteristic zero: the snc-preserving log resolution of the
reduced divisor `Supp D` is a log resolution of `(X, D)`. -/
private theorem exists_isLogResolution {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (D : RDivisor X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), MMP.Mori.IsLogResolution sX D g := by
  obtain ⟨Y, f, hres, hpure, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX D.support
  have hYv : AlgebraicGeometry.IsVariety k (f ≫ sX) := hres.isVariety_source
  have : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (f ≫ sX) := hYv.toQuasiCompact
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : AlgebraicGeometry.IsNoetherian Y := {}
  have hsupp_eq : (D.supp : Set X) = D.support.sup fun E => (E.idealSheaf.support : Set X) := by
    rw [DivisorWithCoeffs.supp, Closeds.coe_finset_sup]
    rfl
  rw [← hsupp_eq] at hS
  refine ⟨Y, f, ⟨⟨hres.isProjective.isProper, hres.isBirationalMorphism, hres.isSmoothScheme⟩,
    hpure, isSNCSubset_of_isSNCClosedSubset _ ?_⟩⟩
  simpa using hS

/-! ### The discrepancy of `(X, Δ + εΔ')` near `ε = 0` -/

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
    · rw [h0] at hF
      exact absurd hF (by simp)
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
  classical
  exact ⟨affineOf 1 0, by simp [affineFamily]⟩

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
  simp only [affineFamily, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_product] at hℓ
  rcases hℓ with rfl | ((⟨G, hG, rfl⟩ | ⟨⟨G, F⟩, ⟨⟨hG, hF⟩, hGF, hmeet⟩, rfl⟩) |
    ⟨G, ⟨hG, hGe⟩, rfl⟩)
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

private theorem exists_discrep_add_smul_eq_inf' {k : Type u} [Field k] [IsAlgClosed k]
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
  -- a log resolution of `(X, Supp Δ ∪ Supp Δ')`
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
  -- the pairs `(X, Δ + εΔ')`
  have hpair : ∀ ε : ℚ, IsPairWith sX n K (Δ + ε • Δ') := fun ε =>
    ⟨hX, hP.2.1, by rw [← add_assoc]; exact hP.2.2.add (MMP.Flips.isQCartier_smul hΔ' ε)⟩
  -- the crepant boundary `Θ_ε = Δ_Y + ε f^*Δ'`
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
  -- the components `S` of the snc divisor `Ex(f) ∪ f⁻¹(Supp A)`
  obtain ⟨S, hsncS, hmemS⟩ := exists_finset_isSNC hf.isSmoothScheme hf.isSNCSubset
  have hexcS : ∀ G : MMP.Mori.PrimeDivisor Y, (DG G).IsExceptional → G ∈ S := fun G hG =>
    hmemS G (Or.inl (MMP.Positivity.support_subset_exceptionalSet G hG
      (MMP.Flips.primeDivisor_genericPoint_mem_support G)))
  -- the coefficients: `θ_E < 1` on exceptional `E`, and `(θ_G, δ_G) = (coeff_P Δ, coeff_P Δ')`
  -- for the strict transform `G` of `P`
  have hexc : ∀ G, (DG G).IsExceptional → θ G < 1 := fun G hG => by
    have := lt_of_lt_of_le hd (discrep_le hG (hΘ G))
    have : ((θ G : ℝ) : EReal) < ((1 : ℝ) : EReal) := by simpa using this
    exact_mod_cast EReal.coe_lt_coe_iff.mp this
  have hnexc : ∀ G, ¬ (DG G).IsExceptional → ∃ P : MMP.Mori.PrimeDivisor X,
      θ G = Δ.coeff P ∧ δ G = Δ'.coeff P ∧ f G.genericPoint = P.genericPoint := by
    intro G hG
    obtain ⟨P, hc0, hη⟩ := exists_coeff_eq_of_not_isExceptional hP hY hfb hΘ hG
    obtain ⟨P', hc1, hη'⟩ := exists_coeff_eq_of_not_isExceptional (hpair 1) hY hfb (hΘε 1) hG
    obtain rfl : P' = P :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hη'.symm.trans hη)
    refine ⟨P', hc0, ?_, hη⟩
    rw [hc, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, one_mul, one_smul] at hc1
    linarith
  have hsuppS : ∀ G, (θ G ≠ 0 ∨ δ G ≠ 0) → G ∈ S := by
    intro G hG0
    by_cases hG : (DG G).IsExceptional
    · exact hexcS G hG
    obtain ⟨P, hθP, hδP, hη⟩ := hnexc G hG
    have hPA : A.coeff P ≠ 0 := by
      have hmem : P ∈ Δ.support ∪ Δ'.support := by
        rw [hθP, hδP] at hG0
        rwa [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      simp [A, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.single_apply,
        hmem]
    refine hmemS G (Or.inr ?_)
    change f G.genericPoint ∈ A.supp
    rw [hη]
    exact DivisorWithCoeffs.support_subset_supp hPA
      (MMP.Flips.primeDivisor_genericPoint_mem_support P)
  -- the radius `ε₁`
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
  -- the formula
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

/-! ### Klt is open under adding a small multiple -/

/-- On a scheme of dimension `≤ 1` no divisor over `X` is exceptional. -/
private theorem not_isExceptional_of_topologicalKrullDim_le_one {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hdim : topologicalKrullDim X ≤ (1 : ℕ))
    (D : DivisorOver k sX) : ¬ D.IsExceptional := by
  intro h
  have hdef : RationalMap.DefinedAt (X := D.Y) D.f.toRationalMap D.E.genericPoint := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (RationalMap.isExceptional_iff.mp h) hdef
  have hmem : D.f D.E.genericPoint ∈
      (RationalMap.transform (X := D.Y) D.f.toRationalMap D.E.idealSheaf.support : Set X) := by
    refine RationalMap.image_subset_transform D.f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨_, ?_, rfl⟩
    change D.E.genericPoint ∈ D.E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hc := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2) _ hmem
  have hle : (Order.coheight (D.f D.E.genericPoint) : WithBot ℕ∞) ≤ (1 : ℕ) := by
    rw [← MMP.Flips.codimension_closureSingleton]
    exact (Order.coheight_le_krullDim _).trans hdim
  have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (1 : ℕ) := (WithBot.coe_le_coe.mpr hc).trans hle
  exact absurd this (by decide)

/-- `-1 < q` in `EReal` exactly when `-1 < q` in `ℚ`. -/
private theorem neg_one_lt_coe_iff (q : ℚ) : (-1 : EReal) < ((q : ℝ) : EReal) ↔ -1 < q := by
  rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp, EReal.coe_lt_coe_iff]
  norm_cast

/-- A minimum of finitely many affine maps `ℚ → ℚ` that is `> -1` at `0` stays `> -1` near `0`. -/
private theorem eventually_neg_one_lt_inf' {L : Finset (ℚ →ᵃ[ℚ] ℚ)} (hL : L.Nonempty)
    (h0 : -1 < L.inf' hL fun ℓ => ℓ 0) : ∀ᶠ ε in 𝓝 (0 : ℚ), -1 < L.inf' hL fun ℓ => ℓ ε :=
  continuousAt_const.eventually_lt
    (Continuous.finset_inf'_apply (f := fun ℓ : ℚ →ᵃ[ℚ] ℚ => ⇑ℓ) hL
      fun ℓ _ => by rw [ℓ.decomp]; fun_prop).continuousAt h0

/-- If every coefficient of `Δ` is `< 1`, so is every coefficient of `Δ + εΔ'` for `ε` near `0`. -/
private theorem eventually_coeff_add_smul_lt_one {X : Scheme.{u}} {Δ Δ' : QDivisor X}
    (hr : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P < 1) :
    ∀ᶠ ε in 𝓝 (0 : ℚ), ∀ P : MMP.Mori.PrimeDivisor X, (Δ + ε • Δ').coeff P < 1 := by
  have := (Filter.eventually_all_finset Δ'.support).2 fun P _ =>
    (show ContinuousAt (fun ε : ℚ => Δ P + ε * Δ' P) 0 by fun_prop).eventually_lt
      continuousAt_const (by simpa [DivisorWithCoeffs.coeff_apply] using hr P)
  filter_upwards [this] with ε hε P
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hP' : P ∈ Δ'.support
  · exact hε P hP'
  · rw [Finsupp.notMem_support_iff.mp hP', mul_zero, add_zero]
    simpa [DivisorWithCoeffs.coeff_apply] using hr P

/-- **The discrepancy stays `> -1`.** If `(X, Δ)` is a pair with `discrep(X, Δ) > -1` and every
coefficient of `Δ` is `< 1`, and `Δ'` is `ℚ`-Cartier, then `discrep(X, Δ + εΔ') > -1` for all
`ε ≥ 0` near `0`. -/
private theorem eventually_neg_one_lt_discrep_add_smul {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ Δ' : QDivisor X}
    (hP : IsPairWith sX n K Δ) (hd : -1 < discrep sX n K Δ)
    (hr : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P < 1) (hΔ'q : Δ'.IsQCartier) :
    ∀ᶠ ε in 𝓝 (0 : ℚ), 0 ≤ ε → -1 < discrep sX n K (Δ + ε • Δ') := by
  rcases le_or_gt 2 n with hn | hn
  · obtain ⟨ε₁, hε₁, L, hL, h0, hεL⟩ := exists_discrep_add_smul_eq_inf' hP hn hd
      (fun P => (hr P).le) hΔ'q (fun P hP1 => absurd hP1 (hr P).ne)
    rw [h0, neg_one_lt_coe_iff] at hd
    filter_upwards [eventually_neg_one_lt_inf' hL hd, eventually_lt_nhds hε₁] with ε hε hεε₁ hε0
    rwa [hεL ε hε0 hεε₁, neg_one_lt_coe_iff]
  · refine Filter.Eventually.of_forall fun ε _ => ?_
    rw [discrep_eq_top fun D a hD _ =>
      not_isExceptional_of_topologicalKrullDim_le_one
        (hP.2.1.topologicalKrullDim_eq.trans_le (by exact_mod_cast (by omega : n ≤ 1))) D hD]
    exact EReal.coe_lt_top (-1)

/-- **Klt is open under adding a small multiple** (Kollár–Mori 2.35(2)). If `(X, Δ)` is klt and
`Δ' ≥ 0` is `ℚ`-Cartier, then `(X, Δ + εΔ')` is klt for all `0 ≤ ε < ε₀`, for some `ε₀ > 0`. -/
private theorem exists_forall_isKltPair_add_smul {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (h : IsKltPair sX n K Δ) {Δ' : QDivisor X} (hΔ'q : Δ'.IsQCartier) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 ≤ ε → ε < ε₀ → IsKltPair sX n K (Δ + ε • Δ') := by
  obtain ⟨hP, hd, hr⟩ := h
  rw [roundDown_nonpos_iff] at hr
  obtain ⟨ε₀, hε₀, hall⟩ := exists_Ico_subset_of_mem_nhds
    ((eventually_coeff_add_smul_lt_one (Δ' := Δ') hr).and
      (eventually_neg_one_lt_discrep_add_smul hP hd hr hΔ'q)) ⟨1, one_pos⟩
  refine ⟨ε₀, hε₀, fun ε h0 hε => ⟨⟨hP.1, hP.2.1, ?_⟩, (hall ⟨h0, hε⟩).2 h0,
    roundDown_nonpos_iff.mpr (hall ⟨h0, hε⟩).1⟩⟩
  rw [← add_assoc]
  exact hP.2.2.add (MMP.Flips.QDivisor.IsQCartier.qsmul hΔ'q ε)

/-! ### The ample core -/

/-- For finitely many positive rationals there is `ε = 1/N ≤ 1` below all of them. -/
private theorem exists_inv_natCast_lt {α : Type*} (s : Finset α) (g : α → ℚ)
    (hg : ∀ x ∈ s, 0 < g x) :
    ∃ N : ℕ, 0 < N ∧ (N : ℚ)⁻¹ ≤ 1 ∧ ∀ x ∈ s, (N : ℚ)⁻¹ < g x := by
  obtain ⟨δ, hδ, hle⟩ := exists_pos_forall_le s (fun _ => True) g fun x hx _ => hg x hx
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 δ⁻¹)
  have h1 : (1 : ℚ) < N := (le_max_left _ _).trans_lt hN
  refine ⟨N, by exact_mod_cast zero_lt_one.trans h1, inv_le_one_of_one_le₀ h1.le,
    fun x hx => (inv_lt_of_inv_lt₀ hδ ((le_max_right _ _).trans_lt hN)).trans_le
      (hle x hx trivial)⟩

private theorem isEffective_smul {Y : Scheme.{u}} {D : QDivisor Y} (hD : D.IsEffective) {ε : ℚ}
    (hε : 0 ≤ ε) : (ε • D).IsEffective :=
  DivisorWithCoeffs.isEffective_iff_nonneg.2
    (smul_nonneg hε (DivisorWithCoeffs.isEffective_iff_nonneg.1 hD))

/-- On a normal `ℚ`-factorial variety, removing an effective `B` from a klt pair `(Y, D + B)`
with `D ≥ 0` leaves a klt pair `(Y, D)`. -/
private theorem isKltPair_of_isKltPair_add {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sY]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] (hY : MMP.Fourfold.IsQFactorial sY)
    {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY n) {D B : QDivisor Y} (hD : D.IsEffective)
    (hB : B.IsEffective) (h : MMP.Mori.IsKltPair sY n K (D + B)) :
    MMP.Fourfold.IsKltPair sY D :=
  have hQ := MMP.Fourfold.isQCartier_of_isQFactorial sY hY
  (MMP.Fourfold.isKltPair_iff_mori_isKltPair sY hK
    ⟨inferInstance, inferInstance, ⟨hY.1, n, K, hK, hQ _⟩, hD⟩).2
    (MMP.Threefold.Mori.IsKltPair.of_add ⟨hY.1, hK, hQ _⟩ hB (hQ _) h)

/-- `ℚ`-linear equivalence `G ∼_ℚ H + E - c w` gives `N⁻¹ (H + E - G) ∼_ℚ (N⁻¹ c) w`. -/
private theorem qLinearlyEquivalent_inv_smul_sub {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsNormal Y] {G H E W : QDivisor Y} {c : ℚ} {N : ℕ} (hN : 0 < N)
    (h : G.QLinearlyEquivalent (H + E - c • W)) :
    ((N : ℚ)⁻¹ • (H + E - G)).QLinearlyEquivalent (((N : ℚ)⁻¹ * c) • W) := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  refine ⟨m * N, Nat.mul_pos hm hN, φ⁻¹, ?_⟩
  rw [MMP.Mori.principalDivisor_inv, map_neg, ← hφ]
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  ext P
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.sub_apply,
    Finsupp.add_apply, Finsupp.neg_apply, smul_eq_mul, zsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- For `0 ≤ ε ≤ 1` and `0 ≤ G ≤ Γ`, `E ≥ 0`, the residual boundary `Γ + ε(H + E - G) - εH`,
which is `Γ - εG + εE`, is effective. -/
private theorem isEffective_add_smul_sub_smul {Y : Scheme.{u}} {Γ H E G : QDivisor Y} {ε : ℚ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hG : G.IsEffective) (hE : E.IsEffective) (hGΓ : G ≤ Γ) :
    (Γ + ε • (H + E - G) - ε • H).IsEffective := fun P => by
  have h1 : G P ≤ Γ P := hGΓ P
  have h2 : 0 ≤ G P := hG P
  have h3 : 0 ≤ E P := hE P
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 hε, mul_nonneg (sub_nonneg.2 hε1) h2, mul_nonneg hε h3]

end MMP.Mori.KltRelativeBigCore

end

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

open MMP.Mori.KltRelativeBigCore in
/-- **An ample core for a polytope of boundaries.** Let `f : Y ⟶ S` be a morphism of projective
varieties over an algebraically closed field `k` of characteristic zero, with `Y` normal and
`ℚ`-factorial, let `G ≥ 0` be an `f`-big `ℚ`-divisor, and let `V` be a finite set of effective
`ℚ`-divisors `Γ ≥ G` with `(Y, Γ)` klt. There are an ample effective `ℚ`-divisor `A'` and a
`ℚ`-divisor `T_Y ∼_ℚ c • f^*T₀` (`T₀` Cartier on `S`, `c ∈ ℚ`) such that `Γ + T_Y - A'` is
effective for every `Γ` in the convex hull of `V`, and `(Y, Γ + T_Y - A')` and `(Y, Γ + T_Y)` are
klt for every `Γ ∈ V`. -/
@[mmp "lem_fourfold_relative_big_core_translation"]
public theorem QDivisor.IsRelativelyBig.exists_isKltPair_add_pullback_sub_isAmple
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {Y S : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sS : S ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k sY] [AlgebraicGeometry.IsProjectiveVariety k sS]
    [IsLocallyNoetherian Y] [CompactSpace Y] [IsNormal Y] (hY : IsQFactorial sY) (f : Y ⟶ S)
    (hf : f ≫ sS = sY) {G : QDivisor Y} (hG : G.IsRelativelyBig f) (hG₀ : G.IsEffective)
    (V : Finset (QDivisor Y)) (_hVeff : ∀ Γ ∈ V, Γ.IsEffective) (hVG : ∀ Γ ∈ V, G ≤ Γ)
    (hVklt : ∀ Γ ∈ V, IsKltPair sY Γ) :
    ∃ A' TY : QDivisor Y, A'.IsAmple ∧ A'.IsEffective ∧
      (∃ (c : ℚ) (T₀ : S.CartierDivisor) (T₀' : Y.CartierDivisor) (w : Divisor Y),
        MMP.Intersection.IsPullback f T₀ T₀' ∧ MMP.Intersection.IsWeilDivisorOfCartier T₀' w ∧
        TY.QLinearlyEquivalent (c • Divisor.toQDivisor w)) ∧
      (∀ Γ ∈ convexHull ℚ (V : Set (QDivisor Y)), (Γ + TY - A').IsEffective) ∧
      ∀ Γ ∈ V, IsKltPair sY (Γ + TY - A') ∧ IsKltPair sY (Γ + TY) := by
  classical
  -- the relative Kodaira decomposition `G ∼_ℚ H + E - c [T₀']`
  obtain ⟨H, E, hHa, hHe, hEe, c, T₀, T₀', w, hT, hw, hlin⟩ :=
    MMP.Mori.QDivisor.IsRelativelyBig.exists_qLinearlyEquivalent_add_sub_pullback sY sS hY f hf hG
  -- at each vertex, klt in the sense of Kollár–Mori, and the radius of `Γ + ε(H + E)`
  have hvert : ∀ Γ ∈ V, ∃ (n : ℕ) (K : Divisor Y), K.IsCanonicalDivisor sY n ∧
      ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 ≤ ε → ε < ε₀ →
        MMP.Mori.IsKltPair sY n K (Γ + ε • (H + E)) := fun Γ hΓ => by
    obtain ⟨-, n, K, hK, -⟩ := (hVklt Γ hΓ).1.isPair
    exact ⟨n, K, hK, exists_forall_isKltPair_add_smul
      ((isKltPair_iff_mori_isKltPair sY hK (hVklt Γ hΓ).1).1 (hVklt Γ hΓ))
      (isQCartier_of_isQFactorial sY hY _)⟩
  choose! n K hK ε₀ hε₀ hε using hvert
  -- a common `ε = 1 / N`, and the divisors `A' = εH`, `T_Y = ε(H + E - G)`
  obtain ⟨N, hN, hε1, hεV⟩ := exists_inv_natCast_lt V ε₀ hε₀
  set ε : ℚ := (N : ℚ)⁻¹ with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hres := fun Γ (hΓ : G ≤ Γ) => isEffective_add_smul_sub_smul (H := H) hε0 hε1 hG₀ hEe hΓ
  refine ⟨ε • H, ε • (H + E - G), ?_, isEffective_smul hHe hε0,
    ⟨ε * c, T₀, T₀', w, hT, hw, qLinearlyEquivalent_inv_smul_sub hN hlin⟩,
    fun Γ hΓ => hres _ (convexHull_min hVG (convex_Ici G) hΓ), fun Γ hΓ => ?_⟩
  · obtain ⟨m, hm, D, hD, hDc, hDa⟩ := hHa
    refine ⟨m * N, Nat.mul_pos hm hN, D, ?_, hDc, hDa⟩
    rw [hD, smul_smul, hεdef]
    push_cast
    rw [mul_inv_cancel_right₀ (by exact_mod_cast hN.ne')]
  · have hbig := hε Γ hΓ ε hε0 (hεV Γ hΓ)
    have hCe := hres _ (hVG Γ hΓ)
    refine ⟨isKltPair_of_isKltPair_add sY hY (hK Γ hΓ) hCe
        ((isEffective_smul hHe hε0).add (isEffective_smul hG₀ hε0))
        (by convert hbig using 1; module),
      isKltPair_of_isKltPair_add sY hY (hK Γ hΓ)
        (by simpa using hCe.add (isEffective_smul hHe hε0))
        (isEffective_smul hG₀ hε0) (by convert hbig using 1; module)⟩

end MMP.Fourfold

end
