module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.MMP.BasepointFree.UniformRelativeFreeness
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import MMP.AlgebraicGeometry.Modules.FiniteLocallyFreeRankOne

/-!
# A nef adjoint with a big rational core is semiample

Let `f : Y ⟶ Z` be a morphism of projective complex varieties, `Y` normal and `ℚ`-factorial,
and let `Γ` be an effective real klt boundary on `Y` containing an effective `ℚ`-divisor `G`
that is big over `Z`. If `D = K_Y + Γ` is nef over `Z`, then `D` defines a contraction: there
are a normal projective variety `T`, a projective contraction `g : Y ⟶ T` over `Z` and an
`ℝ`-Cartier divisor `H` on `T`, ample over `Z`, with `D ∼_ℝ g^* H`. Moreover the positive
degrees of `D` on the curves contracted over `Z` are bounded below by a constant `a > 0`, and
such a curve has `D`-degree zero exactly when `g` contracts it.

## Main results

* `MMP.Fourfold.exists_isContraction_of_isRelativelyNef_of_isRelativelyBig`

## Implementation notes

`D ∼_ℝ g^* H` is stated as: for some (equivalently every) pull-back `g^* H` of the `ℝ`-Cartier
divisor `H` (`MMP.Flips.IsRCartierPullback`), the difference `D - g^* H` is a real linear
combination `∑ rᵢ div(φᵢ)` of principal divisors. Intersection numbers `D · C` are those of
`MMP.Flips.IsRIntersectionNumber`, computed with any presentation of `D` by Cartier divisors;
they do not depend on the presentation. "`Γ` contains `G`" means `Γ - G` is effective.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold

namespace MMP.ChainRealBigAdjointContraction

/-- On a klt pair every boundary coefficient is `< 1`: the log discrepancy `1 - b_P` of a prime
divisor `P` of `Y` is positive. -/
private theorem coeff_lt_one_of_isKltPair {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y} (hΘ : IsKltPair sY Θ)
    (P : MMP.Mori.PrimeDivisor Y) : Θ.coeff P < 1 := by
  obtain ⟨hvar, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hvar P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hvar P).f := by
    change IsProper (𝟙 Y); infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hvar ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

/-- The coefficient of `∑ᵢ vᵢ pᵢ` along `p j`, for an injective family of primes `p`. -/
private theorem coeff_sum_single_apply {R : Type*} [AddCommMonoid R] {Y : Scheme.{0}} {r : ℕ}
    {p : Fin r → MMP.Mori.PrimeDivisor Y} (hp : Function.Injective p) (v : Fin r → R)
    (j : Fin r) :
    DivisorWithCoeffs.coeff (∑ i, Finsupp.single (p i) (v i) : DivisorWithCoeffs R Y) (p j) =
      v j := by
  classical
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single j]
  · exact Finsupp.single_eq_same
  · intro b _ hb
    exact Finsupp.single_eq_of_ne (fun h => hb (hp h.symm))
  · simp

/-- The coefficient of `∑ᵢ vᵢ pᵢ` along a prime outside the range of `p` vanishes. -/
private theorem coeff_sum_single_of_notMem {R : Type*} [AddCommMonoid R] {Y : Scheme.{0}}
    {r : ℕ} (p : Fin r → MMP.Mori.PrimeDivisor Y) (v : Fin r → R)
    {P : MMP.Mori.PrimeDivisor Y} (hP : P ∉ Set.range p) :
    DivisorWithCoeffs.coeff (∑ i, Finsupp.single (p i) (v i) : DivisorWithCoeffs R Y) P = 0 := by
  classical
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne (fun h => hP ⟨i, h.symm⟩)

/-- A nonnegative real combination of Cartier divisors, each with a relatively free positive
multiple, is a positive real combination of relatively free Cartier divisors. -/
private theorem exists_sum_isRelativelyFreeDivisor_of_sum
    {Y Z : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ Z) (H : Finset (Divisor Y))
    (hH : ∀ h ∈ H, h.IsCartier ∧ ∃ p : ℕ, 0 < p ∧ IsRelativelyFreeDivisor f ((p : ℤ) • h))
    (t : Divisor Y → ℝ) (ht : ∀ h, 0 ≤ t h) {D : RDivisor Y}
    (hsum : D = ∑ h ∈ H, t h • Divisor.toRDivisor h) :
    ∃ (s : ℕ) (r : Fin s → ℝ) (L : Fin s → Divisor Y), (∀ i, 0 < r i) ∧
      (∀ i, (L i).IsCartier) ∧ (∀ i, IsRelativelyFreeDivisor f (L i)) ∧
      D = ∑ i, r i • Divisor.toRDivisor (L i) := by
  classical
  choose! q hq0 hqfree using fun h (hh : h ∈ H) => (hH h hh).2
  set H' := H.filter (fun h => 0 < t h)
  have hH'H : ∀ h ∈ H', h ∈ H := fun h hh => (Finset.mem_filter.mp hh).1
  let e' := H'.equivFin
  refine ⟨H'.card, fun j => t (e'.symm j) / q (e'.symm j),
    fun j => ((q (e'.symm j) : ℕ) : ℤ) • (e'.symm j : Divisor Y), fun j => ?_, fun j => ?_,
    fun j => hqfree _ (hH'H _ (e'.symm j).2), ?_⟩
  · exact div_pos (Finset.mem_filter.mp (e'.symm j).2).2
      (by exact_mod_cast hq0 _ (hH'H _ (e'.symm j).2))
  · exact (hH _ (hH'H _ (e'.symm j).2)).1.zsmul _
  · have hterm : ∀ h ∈ H', (t h / q h) • Divisor.toRDivisor (((q h : ℕ) : ℤ) • h) =
        t h • Divisor.toRDivisor h := by
      intro h hh
      have hq : (q h : ℝ) ≠ 0 := by exact_mod_cast (hq0 h (hH'H h hh)).ne'
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast,
        div_mul_cancel₀ _ hq]
    rw [hsum, ← Finset.sum_filter_of_ne (p := fun h => 0 < t h) (fun h _ hne =>
      lt_of_le_of_ne (ht h) (fun h0 => hne (by rw [← h0, zero_smul])))]
    rw [← Finset.sum_coe_sort H', ← e'.symm.sum_comp]
    exact Finset.sum_congr rfl fun j _ => (hterm _ (e'.symm j).2).symm

/-- If `K_Y + Γ` is nef over `Z`, it is a positive real combination of relatively free
Cartier divisors. -/
private theorem exists_sum_isRelativelyFreeDivisor
    {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sY : Y ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sY] (f : Y ⟶ Z)
    (hf : f ≫ sZ = sY) (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYq : IsQFactorial sY)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (n : ℕ) (K : Divisor Y) (hK : K.IsCanonicalDivisor sY n)
    (Γ : RDivisor Y) (hΓ : ∀ P, 0 ≤ Γ.coeff P) (hklt : IsRealKltPair sY Γ)
    (G : QDivisor Y) (hG : ∀ P, 0 ≤ G.coeff P) (hGΓ : ∀ P, (G.coeff P : ℝ) ≤ Γ.coeff P)
    (hbig : G.IsRelativelyBig f)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sY f (MMP.Flips.logCanonicalDivisor K Γ)) :
    ∃ (s : ℕ) (r : Fin s → ℝ) (L : Fin s → Divisor Y), (∀ i, 0 < r i) ∧
      (∀ i, (L i).IsCartier) ∧ (∀ i, IsRelativelyFreeDivisor f (L i)) ∧
      MMP.Flips.logCanonicalDivisor K Γ = ∑ i, r i • Divisor.toRDivisor (L i) := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hY
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  -- enumerate the primes in the supports of `Γ` and `G`
  set S : Finset (MMP.Mori.PrimeDivisor Y) := Γ.support ∪ G.support
  let e := S.equivFin
  let p : Fin S.card → MMP.Mori.PrimeDivisor Y := fun j => (e.symm j : MMP.Mori.PrimeDivisor Y)
  have hp : Function.Injective p := fun a b h => e.symm.injective (Subtype.ext h)
  have hmem : ∀ P ∈ S, P ∈ Set.range p := fun P hP => ⟨e ⟨P, hP⟩, by simp [p]⟩
  have hΓp : ∀ P, Γ.coeff P ≠ 0 → P ∈ Set.range p := fun P hP =>
    hmem P (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr
      (by simpa [DivisorWithCoeffs.coeff_apply] using hP)))
  have hGp : ∀ P, G.coeff P ≠ 0 → P ∈ Set.range p := fun P hP =>
    hmem P (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr
      (by simpa [DivisorWithCoeffs.coeff_apply] using hP)))
  -- a rational klt polytope around `Γ`
  obtain ⟨V, -, hint, hGx, hVklt⟩ := exists_rationalPolytope_isKltPair_of_isRealKltPair sY hY hYq
    Γ hΓ hklt G hG hGΓ p hp hΓp hGp
  -- the vertices as `ℚ`-divisors, and the coordinate map
  let φ : (Fin S.card → ℚ) → QDivisor Y := fun v => ∑ i, Finsupp.single (p i) (v i)
  let V' : Finset (QDivisor Y) := V.image φ
  let Λ : (Fin S.card → ℝ) →ₗ[ℝ] RDivisor Y :=
    { toFun := fun x => ∑ i, Finsupp.single (p i) (x i)
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum] }
  have hΛ : ∀ x, Λ x = ∑ i, Finsupp.single (p i) (x i) := fun _ => rfl
  have hφ : ∀ v, QDivisor.toRDivisor (φ v) = Λ (fun i => (v i : ℝ)) := by
    intro v
    refine DivisorWithCoeffs.ext' fun P => ?_
    rw [QDivisor.coeff_toRDivisor, hΛ]
    by_cases hP : P ∈ Set.range p
    · obtain ⟨j, rfl⟩ := hP
      rw [coeff_sum_single_apply hp, coeff_sum_single_apply hp]
    · rw [coeff_sum_single_of_notMem p _ hP, coeff_sum_single_of_notMem p _ hP, Rat.cast_zero]
  have hΓΛ : Γ = Λ (fun i => Γ.coeff (p i)) := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    rw [hΛ]
    by_cases hP : P ∈ Set.range p
    · obtain ⟨j, rfl⟩ := hP
      rw [coeff_sum_single_apply hp]
    · rw [coeff_sum_single_of_notMem p _ hP]
      by_contra h
      exact hP (hΓp P h)
  have himage : QDivisor.toRDivisor '' (V' : Set (QDivisor Y)) =
      Λ '' ((fun v i => (v i : ℝ)) '' (V : Set (Fin S.card → ℚ))) := by
    simp only [V', Finset.coe_image, Set.image_image, hφ]
  have hΓmem : Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (V' : Set (QDivisor Y))) := by
    rw [himage, ← LinearMap.image_convexHull]
    exact ⟨_, intrinsicInterior_subset hint, hΓΛ.symm⟩
  -- the vertex conditions
  have hvG : ∀ v ∈ V, ∀ i, ((G.coeff (p i) : ℚ) : ℝ) ≤ (v i : ℝ) := fun v hv =>
    hGx _ (subset_convexHull ℝ _ ⟨v, hv, rfl⟩)
  have hVG : ∀ Γ' ∈ V', G ≤ Γ' := by
    intro Γ' hΓ'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hΓ'
    intro P
    change G.coeff P ≤ (φ v).coeff P
    by_cases hP : P ∈ Set.range p
    · obtain ⟨j, rfl⟩ := hP
      rw [coeff_sum_single_apply hp]
      exact_mod_cast hvG v hv j
    · rw [coeff_sum_single_of_notMem p _ hP]
      by_contra h
      exact hP (hGp P fun h0 => h h0.le)
  have hVeff : ∀ Γ' ∈ V', Γ'.IsEffective := fun Γ' hΓ' P =>
    (hG P).trans (hVG Γ' hΓ' P)
  have hVklt' : ∀ Γ' ∈ V', IsKltPair sY Γ' := by
    intro Γ' hΓ'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hΓ'
    exact hVklt v hv
  have hV₁ : ∀ Γ' ∈ V', ∀ E, Γ'.coeff E ≤ 1 := fun Γ' hΓ' E =>
    (coeff_lt_one_of_isKltPair (hVklt' Γ' hΓ') E).le
  -- uniform freeness gives a finite semiample cone containing `K + Γ`
  obtain ⟨VQ, -, -, hΓQ, -, -, H, hH, hcomb⟩ :=
    QDivisor.IsRelativelyBig.exists_isRelativelyFreeDivisor_nsmul_of_isRelativelyNef sY sZ hYq f hf
      ⟨n, hK⟩ hbig hG V' hVeff hV₁ hVG hVklt' hΓmem hnef
  obtain ⟨t, ht, hsum⟩ := hcomb Γ hΓQ
  exact exists_sum_isRelativelyFreeDivisor_of_sum f H hH t ht hsum

/-! ### The Stein factor of a relatively free divisor -/

/-- An epimorphic counit of `f^* ⊣ f_*` stays epimorphic along an isomorphism of modules. -/
private theorem epi_counit_of_iso {X Z : Scheme.{0}} (f : X ⟶ Z) {M N : X.Modules} (e : N ≅ M)
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have heq : adj.counit.app N =
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map e.hom ≫
        adj.counit.app M ≫ e.inv := by
    rw [← Category.assoc, adj.counit.naturality e.hom, Functor.id_map, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

/-- A curve that `g : X ⟶ T` does not contract, `T` a projective variety, maps onto a proper
curve of `T`, with nonzero residue degree. -/
private theorem isProperCurve_and_residueFieldDegree_ne_zero {X T : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} (hT : MMP.Mori.IsProjectiveVariety ℂ sT)
    (g : X ⟶ T) (hg : g ≫ sT = sX) (C : ProperCurve sX) (hC : ¬ C.IsContractedBy g) :
    ∃ _ : IsProperCurve sT (g C.point), residueFieldDegree g C.point ≠ 0 := by
  haveI : AlgebraicGeometry.IsVariety ℂ sT := hT.toIsVariety
  obtain ⟨H, hHi, hH⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hT
  have hne : C.degree ℂ ((Scheme.Modules.pullback g).obj H) ≠ 0 := fun h0 =>
    hC (MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero g hg H hH C h0)
  rw [ProperCurve.degree_pullback g hg C H] at hne
  split_ifs at hne with hD
  · exact ⟨hD, fun h0 => hne (by rw [h0]; simp)⟩
  · exact absurd rfl hne

/-- An `f`-ample Cartier divisor is ample over an affine neighbourhood of every point. -/
private theorem isRelativelyAmple_of_isRelativelyAmpleCartier {X Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {W : Divisor Y}
    (hW : MMP.Flips.IsRelativelyAmpleCartier f W) :
    haveI := hW.1.isInvertibleModule_divisorialSheaf
    MMP.Mori.IsRelativelyAmple f W.divisorialSheaf := by
  obtain ⟨hWc, hamp⟩ := hW
  have := hWc.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨V, hV, hyV, hamp V hV⟩

/-- A curve contracted by `ρ ≫ h` but not by `ρ` has positive degree against the pull-back
along `ρ` of an `h`-ample Cartier divisor. -/
private theorem degree_pullback_pos_of_isRelativelyAmpleCartier {X T Z : Scheme.{0}}
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    {sX : X ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} (hT : MMP.Mori.IsProjectiveVariety ℂ sT)
    (ρ : X ⟶ T) [IsProper ρ] (hρ : ρ ≫ sT = sX) (h : T ⟶ Z) {A : Divisor T}
    (hA : MMP.Flips.IsRelativelyAmpleCartier h A) (C : ProperCurve sX)
    (hCf : C.IsContractedBy (ρ ≫ h)) (hCρ : ¬ C.IsContractedBy ρ) :
    haveI := hA.1.isInvertibleModule_divisorialSheaf
    0 < C.degree ℂ ((Scheme.Modules.pullback ρ).obj A.divisorialSheaf) := by
  haveI := hA.1.isInvertibleModule_divisorialSheaf
  haveI : AlgebraicGeometry.IsVariety ℂ sT := hT.toIsVariety
  obtain ⟨hD, hres⟩ := isProperCurve_and_residueFieldDegree_ne_zero hT ρ hρ C hCρ
  rw [ProperCurve.degree_pullback ρ hρ C, dif_pos hD]
  have hC' : (⟨ρ C.point, hD⟩ : ProperCurve sT).IsContractedBy h := by
    intro x hx
    change x ∈ closure {ρ C.point} at hx
    rw [← Set.image_singleton, ρ.isClosedMap.closure_image_eq_of_continuous ρ.continuous] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [Scheme.Hom.comp_apply] using hCf y hy
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy h _
    (isRelativelyAmple_of_isRelativelyAmpleCartier hA) _ hC'
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hres) hpos

/-- The projection of `ℙ(G) = Proj_Z(Sym G)` is proper when `G` is quasi-coherent of finite
type. -/
private theorem isProper_relativeProj_toBase {Z : Scheme.{0}} (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] :
    IsProper (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
      (Stacks.SymGraded.schemeSheafGradedAlgebra G
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G))).toBase := by
  have h := Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType Z G
  rw [← Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase G] at h
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp h

/-- A Stein factorization `X ⟶ T ⟶ P` of a proper morphism `Φ : X ⟶ P` over `Z`, carrying the
data that `IsRelativelyFreeCartier.steinFactor_isRelativelyAmpleCartier` attaches to every
Stein factorization. -/
private theorem exists_steinFactor {X P Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sX] (sZ : Z ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sZ]
    (πP : P ⟶ Z) (hπ : IsProper πP) (Φ : X ⟶ P) [IsProper Φ] (f : X ⟶ Z) (hΦ : Φ ≫ πP = f)
    (hf : f ≫ sZ = sX) (M : X.Modules)
    (hall : ∀ (YL : Scheme.{0}) (ρ : X ⟶ YL) (τ : YL ⟶ P),
      Stacks.SteinFactorization.IsSteinFactorization Φ ρ τ →
        MMP.Mori.IsNormalVariety ℂ (τ ≫ πP ≫ sZ) ∧
          (∀ U : YL.Opens, IsIso (ρ.app U)) ∧ IsFinite τ ∧
          ∃ (_ : IsLocallyNoetherian YL) (_ : IsNormal YL) (_ : CompactSpace YL)
            (A : Divisor YL), MMP.Flips.IsRelativelyAmpleCartier (τ ≫ πP) A ∧
            Nonempty (M ≅ (Scheme.Modules.pullback ρ).obj A.divisorialSheaf)) :
    ∃ (T : Scheme.{0}) (ρ : X ⟶ T) (h : T ⟶ Z) (_ : MMP.Mori.IsNormalVariety ℂ (h ≫ sZ))
      (_ : ρ ≫ h = f) (_ : IsProper ρ) (_ : Surjective ρ) (_ : IsProper h)
      (_ : ∀ U : T.Opens, IsIso (ρ.app U)) (_ : IsLocallyNoetherian T) (_ : IsNormal T)
      (_ : CompactSpace T) (A : Divisor T),
      MMP.Flips.IsRelativelyAmpleCartier h A ∧
        Nonempty (M ≅ (Scheme.Modules.pullback ρ).obj A.divisorialSheaf) := by
  haveI := hπ
  have hπs : Φ ≫ πP ≫ sZ = sX := by rw [reassoc_of% hΦ, hf]
  obtain ⟨T, ρ, τ, ⟨hSt⟩, hρp, hρs, hρapp, -, hτ, -, -, -, -, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sX (πP ≫ sZ) Φ hπs
  obtain ⟨hTn, -, -, i1, i2, i3, A, hA, hMA⟩ := hall T ρ τ hSt
  haveI := hτ
  have hρh : ρ ≫ τ ≫ πP = f := by rw [← Category.assoc, hSt.comp, hΦ]
  exact ⟨T, ρ, τ ≫ πP, by simpa only [Category.assoc] using hTn, hρh, hρp, hρs,
    inferInstance, hρapp, i1, i2, i3, A, hA, hMA⟩

/-- **The Stein factor of a relatively free divisor.** A relatively free Cartier divisor `L` on
`Y`, over a projective variety `Z`, defines a contraction `ρ : Y ⟶ T` onto a normal projective
variety over `Z` with `𝒪_Y(L) ≅ ρ^* 𝒪_T(A)`, `A` ample over `Z`. On a curve contracted over `Z`,
`L` has nonnegative degree, zero exactly when `ρ` contracts the curve. -/
private theorem exists_steinFactor_of_isRelativelyFreeDivisor
    {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sY : Y ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sY] (f : Y ⟶ Z)
    (hf : f ≫ sZ = sY) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hYn : IsNormalVariety ℂ sY)
    (L : Divisor Y) (hL : L.IsCartier) (hfree : IsRelativelyFreeDivisor f L) :
    ∃ (T : Scheme.{0}) (_ : IsIntegral T) (_ : IsLocallyNoetherian T) (_ : IsNormal T)
      (_ : CompactSpace T) (ρ : Y ⟶ T) (h : T ⟶ Z) (A : Divisor T),
      MMP.Mori.IsProjectiveVariety ℂ (h ≫ sZ) ∧ IsContraction sY (h ≫ sZ) ρ ∧ ρ ≫ h = f ∧
      MMP.Flips.IsRelativelyAmpleCartier h A ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback ρ).obj A.divisorialSheaf) ∧
      ∀ C : ProperCurve sY, C.IsContractedBy f →
        0 ≤ L.degreeOn ℂ sY C.ι C.dim_le hL ∧
          (L.degreeOn ℂ sY C.ι C.dim_le hL = 0 ↔ C.IsContractedBy ρ) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hY
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY.toIsVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZ.toIsVariety
  haveI : IsProper sY := isProper_of_isProjectiveMorphism _ hY.isProjective
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism _ hZ.isProjective
  haveI : IsProper f := by
    haveI : IsProper (f ≫ sZ) := hf ▸ inferInstance
    exact IsProper.of_comp f sZ
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace sZ).mp inferInstance
  haveI : IsNoetherian Z := (isNoetherian_iff Z).mpr ⟨inferInstance, inferInstance⟩
  haveI := hL.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨eE⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L.divisorialSheaf
  have hfreeE : IsRelativelyFreeCartier f E := epi_counit_of_iso f eE.symm hfree
  have key := IsRelativelyFreeCartier.steinFactor_isRelativelyAmpleCartier sY sZ hYn
    hZ.toIsVariety f hf E hfreeE
  dsimp only at key
  obtain ⟨⟨Φ, hΦ, e, hdef⟩, hall⟩ := key
  obtain ⟨hΦp, hall⟩ := hall Φ hΦ e hdef
  haveI : ((Scheme.Modules.pushforward f).obj
      (MMP.CartierDivisor.sheaf E)).IsQuasicoherent :=
    ProperCoherentFiniteType.isQuasicoherent_pushforward f _ inferInstance
  haveI : ((Scheme.Modules.pushforward f).obj
      (MMP.CartierDivisor.sheaf E)).IsFiniteType :=
    (AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f
      (MMP.CartierDivisor.sheaf E)).isFiniteType
  obtain ⟨T, ρ, h, hTn, hρh, hρp, hρs, hhp, hρapp, i1, i2, i3, A, hA, ⟨eA⟩⟩ :=
    exists_steinFactor sY sZ _ (isProper_relativeProj_toBase _) Φ f hΦ hf _
      fun YL ρ τ hS => by
        obtain ⟨h1, h2, h3, i1, i2, i3, A, hA, -, hM⟩ := hall YL ρ τ hS
        exact ⟨h1, h2, h3, i1, i2, i3, A, hA, hM⟩
  haveI : IsIntegral T := hTn.1.toIsIntegral
  haveI : AlgebraicGeometry.IsVariety ℂ (h ≫ sZ) := hTn.1
  haveI := hA.1.isInvertibleModule_divisorialSheaf
  have hcomp : ρ ≫ h ≫ sZ = sY := by rw [reassoc_of% hρh, hf]
  -- `T` is projective
  have hhproj : IsProjective h := MMP.isProjective_of_isProper_of_isRelativelyAmple h _
    (isRelativelyAmple_of_isRelativelyAmpleCartier hA)
  have hT : MMP.Mori.IsProjectiveVariety ℂ (h ≫ sZ) :=
    (isProjectiveVariety_iff_isProjective' ℂ _).mpr ⟨inferInstance,
      IsProjective.comp hhproj ((isProjectiveVariety_iff_isProjective' ℂ sZ).mp hZ).2⟩
  haveI : IsQuasiProjectiveVariety ℂ sY := IsProjectiveVariety.isQuasiProjectiveVariety ℂ sY
  have hρproj : IsProjectiveMorphism ρ :=
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sY (h ≫ sZ) ρ hcomp
  have eL : L.divisorialSheaf ≅ (Scheme.Modules.pullback ρ).obj A.divisorialSheaf := eE ≪≫ eA
  refine ⟨T, inferInstance, i1, i2, i3, ρ, h, A, hT,
    ⟨hYn, hTn, hcomp, hρproj, hρs.surj, hρapp⟩, hρh, hA, ⟨eL⟩, fun C hC => ?_⟩
  have hdeg : L.degreeOn ℂ sY C.ι C.dim_le hL =
      C.degree ℂ ((Scheme.Modules.pullback ρ).obj A.divisorialSheaf) :=
    degreeOn_eq_of_iso ℂ sY C.ι C.dim_le eL
  have hCf : C.IsContractedBy (ρ ≫ h) := hρh ▸ hC
  rw [hdeg]
  by_cases hCρ : C.IsContractedBy ρ
  · rw [ProperCurve.degree_pullback_eq_zero_of_isContractedBy ρ hcomp C hCρ]
    exact ⟨le_rfl, iff_of_true rfl hCρ⟩
  · have hpos := degree_pullback_pos_of_isRelativelyAmpleCartier hT ρ hcomp h hA C hCf hCρ
    exact ⟨hpos.le, iff_of_false hpos.ne' hCρ⟩

/-! ### Sums of relatively free divisors and their degrees -/

/-- The degree of a finite sum of Cartier divisors on a curve is the sum of the degrees. -/
private theorem degreeOn_sum {X C : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {κ : Type*} (s : Finset κ) {D : κ → Divisor X}
    (hD : ∀ j, (D j).IsCartier) (hs : (∑ j ∈ s, D j).IsCartier) :
    (∑ j ∈ s, D j).degreeOn ℂ sX i hdim hs = ∑ j ∈ s, (D j).degreeOn ℂ sX i hdim (hD j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Divisor.degreeOn_zero' ℂ sX i hdim
  | insert j s hj ih =>
    have hs' : (∑ j ∈ s, D j).IsCartier :=
      Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Divisor.isCartier_zero
        (fun j _ => hD j)
    simp only [Finset.sum_insert hj]
    rw [← ih hs', ← Divisor.degreeOn_add ℂ sX i hdim (D j) _ (hD j) hs']

/-- A curve contracted by `g` is contracted by `g ≫ h`. -/
private theorem isContractedBy_comp {X T Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {C : ProperCurve sX} {g : X ⟶ T} (h : T ⟶ Z) (hC : C.IsContractedBy g) :
    C.IsContractedBy (g ≫ h) := fun x hx => by
  simp only [Scheme.Hom.comp_apply, hC x hx]

/-! ### Comparing Stein factors -/

/-- **Two contractions over `Z` with the same contracted curves agree.** If `g : Y ⟶ T` and
`g' : Y ⟶ T'` are contractions over `Z` onto projective varieties contracting the same curves,
then `T ≅ T'` compatibly with `g, g'` and the maps to `Z` (rigidity, applied both ways). -/
private theorem exists_iso_of_isContractedBy_iff {Y Z T T' : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} (sZ : Z ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : Y ⟶ Z} (hf : f ≫ sZ = sY)
    {g : Y ⟶ T} {h : T ⟶ Z} (hT : MMP.Mori.IsProjectiveVariety ℂ (h ≫ sZ))
    (hg : IsContraction sY (h ≫ sZ) g) (hgh : g ≫ h = f)
    {g' : Y ⟶ T'} {h' : T' ⟶ Z} (hT' : MMP.Mori.IsProjectiveVariety ℂ (h' ≫ sZ))
    (hg' : IsContraction sY (h' ≫ sZ) g') (hgh' : g' ≫ h' = f)
    (hC : ∀ C : ProperCurve sY, C.IsContractedBy g ↔ C.IsContractedBy g') :
    ∃ u : T ≅ T', g ≫ u.hom = g' ∧ u.hom ≫ h' = h := by
  haveI : Surjective g := ⟨hg.surjective⟩
  haveI : Surjective g' := ⟨hg'.surjective⟩
  haveI : ∀ U, IsIso (g.c.app U) := fun U => hg.isIso_app U.unop
  haveI : ∀ U, IsIso (g'.c.app U) := fun U => hg'.isIso_app U.unop
  haveI : IsIso g.c := NatIso.isIso_of_isIso_app _
  haveI : IsIso g'.c := NatIso.isIso_of_isIso_app _
  obtain ⟨u, hu, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hY hT hT'
    hg.isProjectiveMorphism hg.comp_eq hg'.comp_eq fun C hCg => (hC C).1 hCg
  obtain ⟨v, hv, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hY hT' hT
    hg'.isProjectiveMorphism hg'.comp_eq hg.comp_eq fun C hCg => (hC C).2 hCg
  have hgg := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hY hT hT
    hg.isProjectiveMorphism hg.comp_eq hg.comp_eq fun _ hCg => hCg
  have hgg' := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hY hT' hT'
    hg'.isProjectiveMorphism hg'.comp_eq hg'.comp_eq fun _ hCg => hCg
  have hgf := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hY hT hZ
    hg.isProjectiveMorphism hg.comp_eq hf fun C hCg => hgh ▸ isContractedBy_comp h hCg
  have huv : u ≫ v = 𝟙 T :=
    hgg.unique (by rw [← Category.assoc, hu, hv]) (Category.comp_id g)
  have hvu : v ≫ u = 𝟙 T' :=
    hgg'.unique (by rw [← Category.assoc, hv, hu]) (Category.comp_id g')
  refine ⟨⟨u, v, huv, hvu⟩, hu, ?_⟩
  exact hgf.unique (by simp only [← Category.assoc, hu, hgh']) hgh

/-- Relative ampleness of a Cartier divisor transported along an isomorphism `u : T ⟶ T'` over
`Z`: if `A` is `h'`-ample and `𝒪_T(B) ≅ u^* 𝒪_{T'}(A)`, then `B` is `(u ≫ h')`-ample. -/
private theorem isRelativelyAmpleCartier_comp_of_iso {T T' Z : Scheme.{0}}
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsLocallyNoetherian T'] [IsNormal T'] [CompactSpace T']
    (u : T ⟶ T') [IsIso u] (h' : T' ⟶ Z) {A : Divisor T'}
    (hA : MMP.Flips.IsRelativelyAmpleCartier h' A) {B : Divisor T} (hB : B.IsCartier)
    (eB : B.divisorialSheaf ≅ (Scheme.Modules.pullback u).obj A.divisorialSheaf) :
    MMP.Flips.IsRelativelyAmpleCartier (u ≫ h') B := by
  obtain ⟨hAc, hAamp⟩ := hA
  haveI := hAc.isInvertibleModule_divisorialSheaf
  refine ⟨hB, fun U hU => ?_⟩
  haveI := hB.isInvertibleModule_divisorialSheaf
  have h1 := Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom (u ∣_ (h' ⁻¹ᵁ U))
    (Stacks.AmpleLocallyClosed.pullbackModule (h' ⁻¹ᵁ U).ι A.divisorialSheaf) (hAamp U hU)
  have e : Stacks.AmpleLocallyClosed.pullbackModule (u ∣_ (h' ⁻¹ᵁ U))
      (Stacks.AmpleLocallyClosed.pullbackModule (h' ⁻¹ᵁ U).ι A.divisorialSheaf) ≅
      Stacks.AmpleLocallyClosed.pullbackModule (u ⁻¹ᵁ (h' ⁻¹ᵁ U)).ι B.divisorialSheaf :=
    (Scheme.Modules.pullbackComp (u ∣_ (h' ⁻¹ᵁ U)) (h' ⁻¹ᵁ U).ι).app A.divisorialSheaf ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι u (h' ⁻¹ᵁ U))).app A.divisorialSheaf ≪≫
      ((Scheme.Modules.pullbackComp (u ⁻¹ᵁ (h' ⁻¹ᵁ U)).ι u).app A.divisorialSheaf).symm ≪≫
      (Scheme.Modules.pullback (u ⁻¹ᵁ (h' ⁻¹ᵁ U)).ι).mapIso eB.symm
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp h1

/-- A divisor ample over `Z` on `T'` transports along an isomorphism `u : T ≅ T'` over `Z`: if
`M ≅ ρ^* A` with `ρ = g ≫ u`, then `M ≅ g^* B` for a Cartier divisor `B` on `T` ample over `Z`. -/
theorem exists_isRelativelyAmpleCartier_of_iso {Y T T' Z : Scheme.{0}}
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral T'] [IsLocallyNoetherian T'] [IsNormal T'] [CompactSpace T']
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (u : T ≅ T') {g : Y ⟶ T} {ρ : Y ⟶ T'} (hu₁ : g ≫ u.hom = ρ) {h : T ⟶ Z} {h' : T' ⟶ Z}
    (hu₂ : u.hom ≫ h' = h) {A : Divisor T'} (hA : MMP.Flips.IsRelativelyAmpleCartier h' A)
    {M : Divisor Y} (eM : M.divisorialSheaf ≅ (Scheme.Modules.pullback ρ).obj A.divisorialSheaf) :
    ∃ B : Divisor T, MMP.Flips.IsRelativelyAmpleCartier h B ∧
      Nonempty (M.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj B.divisorialSheaf) := by
  have hgen : ∀ W : irreducibleComponents T, u.hom (componentGenericPoint T W) ∉ A.supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant u.hom A
  have hBc := hA.1.isCartier_pullback u.hom hgen
  have eB := (Divisor.nonempty_divisorialSheaf_pullback_iso hA.1 u.hom hgen).some
  refine ⟨_, hu₂ ▸ isRelativelyAmpleCartier_comp_of_iso u.hom h' hA hBc eB,
    ⟨eM ≪≫ (Scheme.Modules.pullbackCongr hu₁.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp g u.hom).app _).symm ≪≫
      (Scheme.Modules.pullback g).mapIso eB.symm⟩⟩

/-- A finite family of positive reals has a positive lower bound. -/
private theorem exists_pos_forall_le {s : ℕ} (r : Fin s → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ a : ℝ, 0 < a ∧ ∀ i, a ≤ r i := by
  rcases isEmpty_or_nonempty (Fin s) with _ | _
  · exact ⟨1, one_pos, isEmptyElim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min r
    exact ⟨r i₀, hr i₀, hi₀⟩

/-- Coefficients writing `∑ⱼ rⱼ Lⱼ` as `c₀ M + ∑ᵢ cᵢ (M + N Lᵢ)` with `M = ∑ⱼ Lⱼ` and every
coefficient positive: the coefficient of `Lⱼ` on the right is `c₀ + ∑ᵢ cᵢ + N cⱼ`. -/
private theorem exists_pos_coeff_add_nsmul {s : ℕ} (r : Fin s → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ (N : ℕ) (c₀ : ℝ) (c : Fin s → ℝ), 0 < c₀ ∧ (∀ i, 0 < c i) ∧
      ∀ j, c₀ + ∑ i, c i + N * c j = r j := by
  obtain ⟨a, ha, har⟩ := exists_pos_forall_le r hr
  set R := ∑ i, r i with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => (hr i).le
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R / a)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (by positivity) ha.le) hN
  have hNa : 2 * R < N * a := by rwa [div_lt_iff₀ ha] at hN
  have hNs : (0 : ℝ) < N + s := by positivity
  set S := (N * (a / 2) + R) / (N + s) with hS
  have hSa : S < a := by
    rw [hS, div_lt_iff₀ hNs]
    have : (0 : ℝ) ≤ s * a := by positivity
    nlinarith
  refine ⟨N, a / 2, fun j => (r j - S) / N, half_pos ha,
    fun j => div_pos (sub_pos.2 (hSa.trans_le (har j))) hN0, fun j => ?_⟩
  have hsum : ∑ i, (r i - S) / (N : ℝ) = (R - s * S) / N := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hR]
    simp
  rw [hsum]
  have hSe : S * (N + s) = N * (a / 2) + R := by rw [hS, div_mul_cancel₀ _ hNs.ne']
  field_simp
  nlinarith [hSe]

/-- The linear identity behind `exists_pos_coeff_add_nsmul`:
`c₀ ∑ⱼ Xⱼ + ∑ᵢ cᵢ (∑ⱼ Xⱼ + N Xᵢ) = ∑ⱼ (c₀ + ∑ᵢ cᵢ + N cⱼ) Xⱼ`. -/
private theorem smul_sum_add_sum_smul_add_nsmul {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {s : ℕ} (X : Fin s → E) (N : ℕ) (c₀ : ℝ) (c : Fin s → ℝ) :
    c₀ • ∑ j, X j + ∑ i, c i • (∑ j, X j + (N : ℝ) • X i) =
      ∑ j, (c₀ + ∑ i, c i + N * c j) • X j := by
  simp only [smul_add, Finset.sum_add_distrib, add_smul, Finset.smul_sum, Finset.sum_smul,
    smul_smul]
  rw [Finset.sum_comm (f := fun i j => c i • X j)]
  simp only [mul_comm (c _) (N : ℝ), add_assoc]

/-- For nonnegative integers `lⱼ`, `∑ⱼ lⱼ + N lᵢ = 0` exactly when `∑ⱼ lⱼ = 0`. -/
private theorem sum_add_mul_eq_zero_iff {s : ℕ} (l : Fin s → ℤ) (hl : ∀ j, 0 ≤ l j) (N : ℕ)
    (i : Fin s) : ∑ j, l j + N * l i = 0 ↔ ∑ j, l j = 0 := by
  have h₁ := Finset.single_le_sum (fun j _ => hl j) (Finset.mem_univ i)
  have h₂ : 0 ≤ (N : ℤ) * l i := mul_nonneg (by positivity) (hl i)
  have h₃ := hl i
  constructor
  · intro h
    omega
  · intro h
    rw [h, show l i = 0 by omega, mul_zero, add_zero]

/-- The Stein factorization of the morphism over `Z` defined by finitely many relatively free
Cartier divisors `Lᵢ` is a contraction `g`, `∑ rᵢ Lᵢ` is `ℝ`-linearly equivalent to the pull-back
of a divisor ample over `Z`, and on a curve contracted over `Z` the `Lᵢ` have nonnegative integral
degrees, all zero exactly when `g` contracts the curve. -/
private theorem exists_isContraction_of_isRelativelyFreeDivisor
    {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sY : Y ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sY] (f : Y ⟶ Z)
    (hf : f ≫ sZ = sY) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hYn : IsNormalVariety ℂ sY)
    {s : ℕ} (r : Fin s → ℝ) (L : Fin s → Divisor Y) (hr : ∀ i, 0 < r i)
    (hL : ∀ i, (L i).IsCartier) (hfree : ∀ i, IsRelativelyFreeDivisor f (L i)) :
    ∃ (T : Scheme.{0}) (_ : IsIntegral T) (_ : IsLocallyNoetherian T) (_ : IsNormal T)
      (_ : CompactSpace T) (sT : T ⟶ Spec (.of ℂ)) (g : Y ⟶ T) (h : T ⟶ Z) (H : RDivisor T),
      MMP.Mori.IsProjectiveVariety ℂ sT ∧ IsContraction sY sT g ∧ g ≫ h = f ∧
      MMP.Flips.IsRelativelyAmple h H ∧
      (∃ gH : RDivisor Y, MMP.Flips.IsRCartierPullback g H gH ∧
        ∃ (m : ℕ) (r' : Fin m → ℝ) (φ : Fin m → (RationalFunctions Y)ˣ),
          ∑ i, r i • Divisor.toRDivisor (L i) - gH =
            ∑ i, r' i • Divisor.toRDivisor (principalDivisor (φ i))) ∧
      ∀ C : ProperCurve sY, C.IsContractedBy f →
        ∃ d : Fin s → ℕ, (∀ i, MMP.Flips.IsCartierIntersectionNumber ℂ sY C (L i) (hL i) (d i)) ∧
          ((∀ i, d i = 0) ↔ C.IsContractedBy g) := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hY
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY.toIsVariety
  obtain ⟨N, c₀, c, hc₀, hc, hcr⟩ := exists_pos_coeff_add_nsmul r hr
  -- the divisors `M = ∑ⱼ Lⱼ` and `Mᵢ = M + N Lᵢ`, all relatively free
  obtain ⟨hMc, hMf⟩ := isRelativelyFreeDivisor_sum f Finset.univ hL hfree
  set M : Divisor Y := ∑ j, L j with hMdef
  let Mi : Fin s → Divisor Y := fun i => M + ((N : ℕ) : ℤ) • L i
  have hMic : ∀ i, (Mi i).IsCartier := fun i => hMc.add ((hL i).zsmul _)
  have hMif : ∀ i, IsRelativelyFreeDivisor f (Mi i) := fun i =>
    isRelativelyFreeDivisor_add f hMc ((hL i).zsmul _) hMf
      (isRelativelyFreeDivisor_nsmul f (hL i) (hfree i) N)
  -- their Stein factors
  obtain ⟨T, i1, i2, i3, i4, g, h, A₀, hT, hg, hgh, hA₀, ⟨eM⟩, hMdeg⟩ :=
    exists_steinFactor_of_isRelativelyFreeDivisor sY sZ f hf hY hZ hYn M hMc hMf
  choose Ti j1 j2 j3 j4 ρ hi A hTi hρ hρh hA eMi hMideg using fun i =>
    exists_steinFactor_of_isRelativelyFreeDivisor sY sZ f hf hY hZ hYn (Mi i) (hMic i) (hMif i)
  have hLnn : ∀ j (C : ProperCurve sY), C.IsContractedBy f →
      0 ≤ (L j).degreeOn ℂ sY C.ι C.dim_le (hL j) := fun j C hC => by
    obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, hdeg⟩ :=
      exists_steinFactor_of_isRelativelyFreeDivisor sY sZ f hf hY hZ hYn (L j) (hL j) (hfree j)
    exact (hdeg C hC).1
  -- degrees on curves contracted over `Z`
  have hdegM : ∀ C : ProperCurve sY, M.degreeOn ℂ sY C.ι C.dim_le hMc =
      ∑ j, (L j).degreeOn ℂ sY C.ι C.dim_le (hL j) := fun C =>
    degreeOn_sum sY C.ι C.dim_le Finset.univ hL hMc
  have hM0 : ∀ C : ProperCurve sY, C.IsContractedBy f →
      (M.degreeOn ℂ sY C.ι C.dim_le hMc = 0 ↔
        ∀ j, (L j).degreeOn ℂ sY C.ι C.dim_le (hL j) = 0) := fun C hC => by
    rw [hdegM, Finset.sum_eq_zero_iff_of_nonneg fun j _ => hLnn j C hC]
    simp
  have hMi0 : ∀ i (C : ProperCurve sY), C.IsContractedBy f →
      ((Mi i).degreeOn ℂ sY C.ι C.dim_le (hMic i) = 0 ↔
        M.degreeOn ℂ sY C.ι C.dim_le hMc = 0) := fun i C hC => by
    rw [Divisor.degreeOn_add ℂ sY C.ι C.dim_le M _ hMc ((hL i).zsmul _),
      MMP.Fourfold.degreeOn_zsmul sY C.ι C.dim_le (L i) (hL i), hdegM]
    exact sum_add_mul_eq_zero_iff _ (fun j => hLnn j C hC) N i
  -- all the Stein factors are the same contraction
  have hcurve : ∀ i (C : ProperCurve sY), C.IsContractedBy g ↔ C.IsContractedBy (ρ i) := by
    intro i C
    constructor
    · intro hCg
      have hCf : C.IsContractedBy f := hgh ▸ isContractedBy_comp h hCg
      exact ((hMideg i C hCf).2).mp (((hMi0 i C hCf).2) (((hMdeg C hCf).2).mpr hCg))
    · intro hCρ
      have hCf : C.IsContractedBy f := hρh i ▸ isContractedBy_comp (hi i) hCρ
      exact ((hMdeg C hCf).2).mp (((hMi0 i C hCf).1) (((hMideg i C hCf).2).mpr hCρ))
  choose u hu1 hu2 using fun i =>
    exists_iso_of_isContractedBy_iff sZ hY hZ hf hT hg hgh (hTi i) (hρ i) (hρh i) (hcurve i)
  choose B hBamp eMB using fun i => haveI := j1 i; haveI := j2 i; haveI := j3 i; haveI := j4 i
    exists_isRelativelyAmpleCartier_of_iso (u i) (hu1 i) (hu2 i) (hA i) (eMi i).some
  -- the families indexed by `Fin (s + 1)`: `M, Mᵢ` on `Y` and `A₀, Bᵢ` on `T`
  let κ : Fin (s + 1) → ℝ := Fin.cons c₀ c
  let 𝔅 : Fin (s + 1) → Divisor T := Fin.cons A₀ B
  let 𝔐 : Fin (s + 1) → Divisor Y := Fin.cons M Mi
  have hκ : ∀ k, 0 < κ k := Fin.cases hc₀ hc
  have h𝔅amp : ∀ k, MMP.Flips.IsRelativelyAmpleCartier h (𝔅 k) := Fin.cases hA₀ hBamp
  have h𝔅c : ∀ k, (𝔅 k).IsCartier := fun k => (h𝔅amp k).1
  have e𝔐 : ∀ k, Nonempty ((𝔐 k).divisorialSheaf ≅
      (Scheme.Modules.pullback g).obj (𝔅 k).divisorialSheaf) := Fin.cases ⟨eM⟩ eMB
  -- pull the `𝔅 k` back along `g`
  haveI : Surjective g := ⟨hg.surjective⟩
  have hgen : ∀ k, ∀ W : irreducibleComponents Y, g (componentGenericPoint Y W) ∉ (𝔅 k).supp :=
    fun k W => map_componentGenericPoint_notMem_supp_of_isDominant g (𝔅 k) W
  let 𝔅' : Fin (s + 1) → Divisor Y := fun k => (𝔅 k).pullback (h𝔅c k) (hgen k)
  have e𝔅' : ∀ k, Nonempty ((𝔅' k).divisorialSheaf ≅
      (Scheme.Modules.pullback g).obj (𝔅 k).divisorialSheaf) := fun k =>
    Divisor.nonempty_divisorialSheaf_pullback_iso (h𝔅c k) g (hgen k)
  have hlin : ∀ k, (𝔐 k).LinearlyEquivalent (𝔅' k) := fun k =>
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso ((e𝔐 k).some ≪≫ (e𝔅' k).some.symm)
  choose φ hφ using hlin
  -- `∑ rᵢ Lᵢ = c₀ M + ∑ cᵢ Mᵢ`
  have hsum : ∑ i, r i • Divisor.toRDivisor (L i) =
      ∑ k, κ k • Divisor.toRDivisor (𝔐 k) := by
    rw [Fin.sum_univ_succ]
    simp only [κ, 𝔐, Fin.cons_zero, Fin.cons_succ]
    have hMi : ∀ i, Divisor.toRDivisor (Mi i) =
        ∑ j, Divisor.toRDivisor (L j) + (N : ℝ) • Divisor.toRDivisor (L i) := fun i => by
      simp only [Mi, hMdef, map_add, map_sum, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ,
        Int.cast_natCast]
    rw [Finset.sum_congr rfl fun i _ => congrArg (c i • ·) (hMi i), hMdef, map_sum,
      smul_sum_add_sum_smul_add_nsmul]
    exact Finset.sum_congr rfl fun j _ => by rw [hcr j]
  refine ⟨T, i1, i2, i3, i4, h ≫ sZ, g, h, ∑ k, κ k • Divisor.toRDivisor (𝔅 k), hT, hg, hgh,
    ⟨s + 1, κ, 𝔅, by omega, hκ, h𝔅amp, rfl⟩, ⟨∑ k, κ k • Divisor.toRDivisor (𝔅' k),
      ⟨s + 1, κ, 𝔅, 𝔅', h𝔅c, rfl,
        fun k => ⟨hgen k, Divisor.isPullback_pullback (h𝔅c k) (hgen k)⟩, rfl⟩,
      s + 1, κ, φ, ?_⟩, fun C hC => ?_⟩
  · rw [hsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_sub, ← map_sub, hφ k]
  · refine ⟨fun j => ((L j).degreeOn ℂ sY C.ι C.dim_le (hL j)).toNat, fun j => ?_, ?_⟩
    · rw [Int.toNat_of_nonneg (hLnn j C hC)]
      exact MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sY C (L j) (hL j)
    · rw [← (hMdeg C hC).2, hM0 C hC]
      refine forall_congr' fun j => ?_
      have := hLnn j C hC
      simp only [Int.toNat_eq_zero]
      omega

/-- A positive combination `D = ∑ rᵢ Lᵢ` of Cartier divisors with nonnegative integral degrees
`dᵢ` on a curve `C` has `D · C = 0` or `D · C ≥ a` for any `0 < a ≤ minᵢ rᵢ`, and `D · C = 0`
exactly when every `dᵢ` vanishes. -/
private theorem isRIntersectionNumber_eq_zero_or_le
    {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ))
    [QuasiCompact sX] (C : ProperCurve sX) (D : RDivisor X) {s : ℕ} (r : Fin s → ℝ)
    (L : Fin s → Divisor X) (hL : ∀ i, (L i).IsCartier)
    (hD : D = ∑ i, r i • Divisor.toRDivisor (L i)) (d : Fin s → ℕ)
    (hd : ∀ i, MMP.Flips.IsCartierIntersectionNumber ℂ sX C (L i) (hL i) (d i))
    (a : ℝ) (hr : ∀ i, 0 < r i) (ha : ∀ i, a ≤ r i)
    {m : ℕ} (r' : Fin m → ℝ) (L' : Fin m → Divisor X) (x : ℝ)
    (hx : MMP.Flips.IsRIntersectionNumber ℂ sX D r' L' C x) :
    (x = 0 ∨ a ≤ x) ∧ (x = 0 ↔ ∀ i, d i = 0) := by
  have h0 : MMP.Flips.IsRIntersectionNumber ℂ sX D r L C (∑ i, r i * ((d i : ℤ) : ℝ)) :=
    ⟨hL, fun i => (d i : ℤ), hD, hd, rfl⟩
  have hxe : x = ∑ i, r i * (d i : ℝ) := by
    simpa using (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX C).1 D r' L' r L _ _ hx h0
  subst hxe
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ r i * (d i : ℝ) :=
    fun i _ => mul_nonneg (hr i).le (Nat.cast_nonneg _)
  have hiff : (∑ i, r i * (d i : ℝ)) = 0 ↔ ∀ i, d i = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
    simp [(hr _).ne']
  refine ⟨?_, hiff⟩
  by_cases hall : ∀ i, d i = 0
  · exact Or.inl (hiff.2 hall)
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    right
    calc a ≤ r j := ha j
      _ ≤ r j * (d j : ℝ) :=
        le_mul_of_one_le_right (hr j).le (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj)
      _ ≤ ∑ i, r i * (d i : ℝ) :=
        Finset.single_le_sum hnn (Finset.mem_univ j)

end MMP.ChainRealBigAdjointContraction

namespace MMP.Fourfold

open MMP.Mori MMP.ChainRealBigAdjointContraction

/-- **A nef adjoint with a big rational core defines a contraction.** Let `f : Y ⟶ Z` be a
morphism of projective complex varieties over `ℂ`, with `Y` normal and `ℚ`-factorial, `K` a
canonical divisor of `Y`, and `Γ` an effective real klt boundary with `G ≤ Γ` for an effective
`ℚ`-divisor `G` big over `Z`. If `D = K + Γ` is nef over `Z`, there are a normal projective
variety `T`, a contraction `g : Y ⟶ T` (`MMP.Fourfold.IsContraction`) and `h : T ⟶ Z` with
`g ≫ h = f`, and an `ℝ`-Cartier divisor `H` on `T`, ample over `Z`, such that `D - g^* H` is a
real combination of principal divisors; and there is `a > 0` such that every curve `C`
contracted by `f` has `D · C = 0` or `D · C ≥ a`, with `D · C = 0` if and only if `g`
contracts `C`. -/
@[mmp "lem_fourfold_real_big_adjoint_contraction"]
public theorem exists_isContraction_of_isRelativelyNef_of_isRelativelyBig
    {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sY : Y ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sY] (f : Y ⟶ Z)
    (hf : f ≫ sZ = sY) (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYq : IsQFactorial sY)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (n : ℕ) (K : Divisor Y) (hK : K.IsCanonicalDivisor sY n)
    (Γ : RDivisor Y) (hΓ : ∀ P, 0 ≤ Γ.coeff P) (hklt : IsRealKltPair sY Γ)
    (G : QDivisor Y) (hG : ∀ P, 0 ≤ G.coeff P) (hGΓ : ∀ P, (G.coeff P : ℝ) ≤ Γ.coeff P)
    (hbig : G.IsRelativelyBig f)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sY f (MMP.Flips.logCanonicalDivisor K Γ)) :
    ∃ (T : Scheme.{0}) (_ : IsIntegral T) (_ : IsLocallyNoetherian T) (_ : IsNormal T)
      (_ : CompactSpace T) (sT : T ⟶ Spec (.of ℂ)) (g : Y ⟶ T) (h : T ⟶ Z) (H : RDivisor T),
      MMP.Mori.IsProjectiveVariety ℂ sT ∧ IsContraction sY sT g ∧ g ≫ h = f ∧
      MMP.Flips.IsRelativelyAmple h H ∧
      (∃ gH : RDivisor Y, MMP.Flips.IsRCartierPullback g H gH ∧
        ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions Y)ˣ),
          MMP.Flips.logCanonicalDivisor K Γ - gH =
            ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i))) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ C : ProperCurve sY, C.IsContractedBy f →
        ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y) (x : ℝ),
          MMP.Flips.IsRIntersectionNumber ℂ sY (MMP.Flips.logCanonicalDivisor K Γ) r L C x →
            (x = 0 ∨ a ≤ x) ∧ (x = 0 ↔ C.IsContractedBy g) := by
  obtain ⟨s, r, L, hr, hL, hfree, hD⟩ := exists_sum_isRelativelyFreeDivisor sY sZ f hf hY hYq hZ
    n K hK Γ hΓ hklt G hG hGΓ hbig hnef
  obtain ⟨T, i1, i2, i3, i4, sT, g, h, H, hT, hg, hgh, hH, hlin, hdeg⟩ :=
    exists_isContraction_of_isRelativelyFreeDivisor sY sZ f hf hY hZ hklt.1 r L hr hL hfree
  obtain ⟨a, ha, har⟩ := exists_pos_forall_le r hr
  refine ⟨T, i1, i2, i3, i4, sT, g, h, H, hT, hg, hgh, hH, hD ▸ hlin, a, ha, ?_⟩
  intro C hC m r' L' x hx
  obtain ⟨d, hd, hdg⟩ := hdeg C hC
  obtain ⟨h1, h2⟩ := isRIntersectionNumber_eq_zero_or_le sY C _ r L hL hD d hd a hr har r' L' x hx
  exact ⟨h1, h2.trans hdg⟩

end MMP.Fourfold
