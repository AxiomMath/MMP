module

public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RationalCurveSmoothLocus
public import MMP.AlgebraicGeometry.Intersection.AmpleDegreePositive
public import MMP.AlgebraicGeometry.FiberSpace.FibreComponentSubadjunction
public import MMP.AlgebraicGeometry.IdealSheafSubscheme
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorAdjunction
public import MMP.AlgebraicGeometry.Intersection.SelfIntersectionHilbertDegree
public import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC

section

/-!
# Bounded rational curves in the fibres of a klt contraction

Let `(X, B)` be a klt pair with `B` an effective `ℚ`-divisor and `X` a projective complex variety
of dimension `n ≥ 1`, and let `f : X ⟶ Z` be a contraction which is not an isomorphism and such
that `-(K_X + B)` is `f`-ample. Then `f` has a positive-dimensional fibre over a closed point, and
every such fibre `F` contains a rational curve `T` with `0 < -(K_X + B) · T ≤ 2n`. If `f` is the
contraction of an extremal ray `R` of `NE̅(X)`, then `R = ℝ_{≥0} · [T]`.

A maximal-dimensional component `E` of `F` of dimension `r` is treated by cases: for `r = 1`
weak subadjunction makes `E` a rational curve of degree at most `2`; for `2 ≤ r` a general
complete intersection curve on the normalization of `E` (or on `X` when `r = n`) has negative
canonical degree, and the slope bound on the smooth locus produces a rational curve of
`-(K_X + B)`-degree at most `2r ≤ 2n`.

## Main results

* `MMP.Fourfold.exists_isRationalCurve_of_isContraction_of_isRelativelyAmple_neg`: the statement
  above.

## Implementation notes

* The klt condition is `MMP.Mori.IsKltPair` with a canonical divisor `K` of dimension `n`; this
  pins `n = dim X`. Effectivity of `B` is `0 ≤ B`.
* The contraction is `MMP.Fourfold.IsContraction` (projective, surjective, normal varieties,
  `f_* 𝒪_X = 𝒪_Z`); nontriviality is `¬ IsIso f`. Relative ampleness of the `ℚ`-Cartier divisor
  `-(K_X + B)` is `MMP.Flips.IsRelativelyAmple` of its image as an `ℝ`-divisor.
* The fibres are the sets `f⁻¹(z)` over closed points `z`, with their subspace topology; "of
  positive dimension" is `0 < topologicalKrullDim (f⁻¹(z))`.
* The curve `T` is a `MMP.Mori.ProperCurve`, recorded by its generic point, whose closure lies
  in `f⁻¹(z)` and whose reduced closed subscheme is a rational curve in the sense of
  `MMP.Mori.IsRationalCurve`. The degree `(K_X + B) · T` is `MMP.Fourfold.QDivisor.curveForm`
  evaluated on the class of `T` in `N₁(X)_ℝ`.
* The conclusion also records that a positive-dimensional fibre exists, which is where the
  nontriviality of `f` enters.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace MMP.FourfoldProofs.FourfoldProjectiveComplexKltContractionLengthProof

section Ray

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A nonzero vector of an extremal ray spans it. -/
private theorem eq_ray_of_mem {N R : Set V} (hR : IsExtremalRay ℝ N R) {u : V} (hu : u ∈ R)
    (hu0 : u ≠ 0) : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • u = w} := by
  obtain ⟨-, v, hv, rfl⟩ := hR
  obtain ⟨a, ha, rfl⟩ := hu
  have ha' : 0 < a := lt_of_le_of_ne ha (by rintro rfl; simp at hu0)
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c / a, div_nonneg hc ha, by rw [smul_smul, div_mul_cancel₀ _ ha'.ne']⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c * a, mul_nonneg hc ha, by rw [smul_smul]⟩

end Ray

section Rational

/-- A real point with positive coordinates has a rational point with positive coordinates in its
smallest rational affine hull. -/
private theorem exists_pos_rat_mem_rationalAffineHull {r : ℕ} (δ : Fin r → ℝ)
    (hδ : ∀ j, 0 < δ j) :
    ∃ q : Fin r → ℚ, (∀ j, 0 < q j) ∧ (fun j => (q j : ℝ)) ∈ rationalAffineHull δ := by
  obtain ⟨m, p, e, -, -, hchar⟩ := exists_rational_frame δ
  obtain ⟨s, hs⟩ := (hchar δ).1 (self_mem_rationalAffineHull δ)
  let φ : (Fin m → ℝ) → (Fin r → ℝ) := fun s j => (p j : ℝ) + ∑ i, s i * (e i j : ℝ)
  have hφc : Continuous φ := by
    refine continuous_pi fun j => ?_
    fun_prop
  let U : Set (Fin m → ℝ) := φ ⁻¹' {x | ∀ j, 0 < x j}
  have hU : IsOpen U := by
    refine hφc.isOpen_preimage _ ?_
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_apply j)
  have hsU : s ∈ U := by
    change ∀ j, 0 < φ s j
    rw [show φ s = δ from hs.symm]; exact hδ
  have hdense : DenseRange (fun t : Fin m → ℚ => fun i => (t i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  obtain ⟨t, ht⟩ := hdense.exists_mem_open hU ⟨s, hsU⟩
  refine ⟨fun j => p j + ∑ i, t i * e i j, fun j => ?_, ?_⟩
  · have := ht j
    simp only [φ] at this
    exact_mod_cast this
  · refine (hchar _).2 ⟨fun i => (t i : ℝ), ?_⟩
    ext j
    push_cast
    rfl

/-- **Rational presentation of a relatively ample `ℚ`-divisor.** If a `ℚ`-divisor `D` is a
positive real combination of Cartier divisors `Aⱼ` with a property `P`, then some positive
multiple `N D` is a positive integral combination of the same `Aⱼ`. -/
private theorem exists_nat_presentation {X : Scheme.{0}} {P : Divisor X → Prop} {D : QDivisor X}
    (h : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), 1 ≤ m ∧ (∀ j, 0 < r j) ∧
      (∀ j, P (L j)) ∧ QDivisor.toRDivisor D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    ∃ (m : ℕ) (A : Fin m → Divisor X) (c : Fin m → ℕ) (N : ℕ), 1 ≤ m ∧ 0 < N ∧
      (∀ j, 0 < c j) ∧ (∀ j, P (A j)) ∧
      Divisor.toQDivisor (∑ j, c j • A j) = (N : ℤ) • D := by
  obtain ⟨m, a, A, hm, ha, hA, hD⟩ := h
  obtain ⟨q, hq, hqW⟩ := exists_pos_rat_mem_rationalAffineHull a ha
  -- the rational coefficients present `D`
  have hqD : ∀ E : MMP.Mori.PrimeDivisor X, D E = ∑ j, q j * (A j E : ℚ) := by
    intro E
    have hE := congrArg (fun G : RDivisor X => G E) hD
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at hE
    have hE' : ((D E : ℚ) : ℝ) = ∑ j, a j * ((A j E : ℤ) : ℝ) := hE
    have h0 : ratAffineForm ((fun j => (A j E : ℚ)), -D E) a = 0 := by
      simp only [ratAffineForm, Rat.cast_intCast, Rat.cast_neg, hE']
      rw [← sub_eq_add_neg, sub_eq_zero]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h1 := hqW _ h0
    simp only [ratAffineForm, Rat.cast_intCast, Rat.cast_neg] at h1
    have h3 : ((∑ j, (A j E : ℚ) * q j + -D E : ℚ) : ℝ) = 0 := by push_cast; exact h1
    have h4 : ∑ j, (A j E : ℚ) * q j + -D E = 0 := by exact_mod_cast h3
    rw [show ∑ j, q j * (A j E : ℚ) = ∑ j, (A j E : ℚ) * q j from
      Finset.sum_congr rfl fun j _ => mul_comm _ _]
    linarith
  -- clear denominators
  set N : ℕ := ∏ j, (q j).den with hN
  have hNpos : 0 < N := Finset.prod_pos fun j _ => (q j).den_pos
  have hden : ∀ j, (q j).den ∣ N := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let c : Fin m → ℕ := fun j => (q j).num.toNat * (N / (q j).den)
  have hc : ∀ j, (c j : ℚ) = q j * N := by
    intro j
    have hnum : 0 < (q j).num := Rat.num_pos.mpr (hq j)
    have hd : ((N / (q j).den : ℕ) : ℚ) = N / (q j).den := by
      rw [Nat.cast_div (hden j) (by exact_mod_cast (q j).den_nz)]
    have hnat : (((q j).num.toNat : ℕ) : ℚ) = ((q j).num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum.le
    simp only [c]
    rw [Nat.cast_mul, hnat, hd]
    conv_rhs => rw [← Rat.num_div_den (q j)]
    have : ((q j).den : ℚ) ≠ 0 := by exact_mod_cast (q j).den_nz
    field_simp
  refine ⟨m, A, c, N, hm, hNpos, fun j => ?_, hA, ?_⟩
  · have : (0 : ℚ) < c j := by rw [hc]; exact mul_pos (hq j) (by exact_mod_cast hNpos)
    exact_mod_cast this
  · ext E
    change ((∑ j, c j • A j) E : ℚ) = ((N : ℤ) • D) E
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      zsmul_eq_mul, nsmul_eq_mul]
    push_cast
    rw [hqD E, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc]
    ring

/-- A nonnegative integral combination of Cartier divisors is Cartier. -/
private theorem isCartier_sum_nsmul {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] {m : ℕ}
    (A : Fin m → Divisor X) (hA : ∀ j, (A j).IsCartier) (c : Fin m → ℕ) (s : Finset (Fin m)) :
    (∑ j ∈ s, c j • A j).IsCartier := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Divisor.isCartier_zero
  | insert j s hj ih => rw [Finset.sum_insert hj]; exact ((hA j).nsmul _).add ih

/-- The degree of a positive integral combination of Cartier divisors along a curve. -/
private theorem degreeOn_sum_nsmul {k : Type} [Field k] {X C : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (i : C ⟶ X) [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) {m : ℕ}
    (A : Fin m → Divisor X) (hA : ∀ j, (A j).IsCartier) (c : Fin m → ℕ) (s : Finset (Fin m)) :
    ∃ h : (∑ j ∈ s, c j • A j).IsCartier,
      (∑ j ∈ s, c j • A j).degreeOn k sX i hdim h =
        ∑ j ∈ s, (c j : ℤ) * (A j).degreeOn k sX i hdim (hA j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using Divisor.isCartier_zero, by
      simpa using Divisor.degreeOn_zero' k sX i hdim⟩
  | insert j s hj ih =>
    obtain ⟨h, hs⟩ := ih
    have hj' : (c j • A j).IsCartier := (hA j).nsmul _
    have hsum : (∑ l ∈ insert j s, c l • A l) = c j • A j + ∑ l ∈ s, c l • A l :=
      Finset.sum_insert hj
    refine ⟨hsum ▸ hj'.add h, ?_⟩
    rw [Divisor.degreeOn_congr hsum _ (hj'.add h), Divisor.degreeOn_add k sX i hdim _ _ hj' h,
      hs, Divisor.degreeOn_nsmul', Finset.sum_insert hj]

/-- **Negativity on contracted curves.** If `-D` is `f`-ample, then `D · C < 0` for every proper
curve `C` contracted by `f`. -/
private theorem intersectionNumber_neg_of_isRelativelyAmple {k : Type} [Field k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {Z : Scheme.{0}} {f : X ⟶ Z} {D : QDivisor X}
    (hD : D.IsQCartier) (hamp : MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor (-D)))
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    D.intersectionNumber k sX C.ι C.dim_le hD < 0 := by
  obtain ⟨m, A, c, N, hm, hN, hc, hA, hE⟩ := exists_nat_presentation hamp
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  obtain ⟨hEc, hdeg⟩ := degreeOn_sum_nsmul (k := k) (sX := sX) C.ι C.dim_le A hAc c Finset.univ
  set E := ∑ j, c j • A j with hEdef
  have hE' : Divisor.toQDivisor (-E) = ((N : ℕ) : ℤ) • D := by
    rw [map_neg, hE, smul_neg, neg_neg]
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le D hD hN (-E) hEc.neg hE']
  have h0 := Divisor.degreeOn_add k sX C.ι C.dim_le E (-E) hEc hEc.neg
  rw [Divisor.degreeOn_congr (add_neg_cancel E) _ Divisor.isCartier_zero,
    Divisor.degreeOn_zero'] at h0
  have hpos : 0 < E.degreeOn k sX C.ι C.dim_le hEc := by
    rw [hdeg]
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    refine Finset.sum_pos (fun j _ => mul_pos (by exact_mod_cast hc j) ?_) Finset.univ_nonempty
    obtain ⟨hAj, hampj⟩ := hA j
    haveI := hAj.isInvertibleModule_divisorialSheaf
    have hrel : MMP.Mori.IsRelativelyAmple f (A j).divisorialSheaf := fun y => by
      obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
      exact ⟨V, hV, hyV, hampj V hV⟩
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy
      (sX := sX) f _ hrel C hC
  have : ((-E).degreeOn k sX C.ι C.dim_le hEc.neg : ℚ) < 0 := by
    have : (-E).degreeOn k sX C.ι C.dim_le hEc.neg < 0 := by linarith
    exact_mod_cast this
  exact div_neg_of_neg_of_pos this (by exact_mod_cast hN)

end Rational

section Ample

/-- **Pull-back of a relatively ample divisor to a finite scheme over a point.** If `A` is an
`f`-ample Cartier divisor and `g : V ⟶ X` is finite with image in the fibre of `f` over `z`, then
`g^* 𝒪_X(A)` is ample on `V`. -/
private theorem isAmple_pullback_of_isRelativelyAmpleCartier {V X Z : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Z} {A : Divisor X}
    (hA : MMP.Flips.IsRelativelyAmpleCartier f A) (g : V ⟶ X) [IsFinite g] (z : Z)
    (hgz : ∀ v, f (g v) = z) :
    haveI := hA.1.isInvertibleModule_divisorialSheaf
    Scheme.Modules.IsAmple V ((Scheme.Modules.pullback g).obj A.divisorialSheaf) := by
  obtain ⟨hAc, hamp⟩ := hA
  haveI := hAc.isInvertibleModule_divisorialSheaf
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ z)
  have hrange : Set.range g ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (g v) ∈ U
    rw [hgz v]; exact hzU
  set j := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι g hrange with hjdef
  have hj : j ≫ (f ⁻¹ᵁ U).ι = g := IsOpenImmersion.lift_fac _ _ _
  have : IsFinite (j ≫ (f ⁻¹ᵁ U).ι) := by rw [hj]; infer_instance
  have : IsFinite j := IsFinite.of_comp j (f ⁻¹ᵁ U).ι
  set M := (RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
    A.divisorialSheaf with hM
  have hMinv : SheafOfModules.IsInvertible (f ⁻¹ᵁ U).toScheme.presheaf
      (f ⁻¹ᵁ U).toScheme.ringCatSheaf.2 M :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (f ⁻¹ᵁ U).ι.toLRSHom.toShHom _ inferInstance
  have h1 : Scheme.Modules.IsAmple (f ⁻¹ᵁ U).toScheme M :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr (hamp U hU)
  have h2 := isAmple_pullback_of_isFinite j M h1
  have := MMP.Mori.isInvertible_pullback_obj j M
  let e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback g).obj A.divisorialSheaf :=
    (Scheme.Modules.pullback j).mapIso
        ((AlgebraicGeometry.modulePullbackIsoSchemePullback (f ⁻¹ᵁ U).ι).app _) ≪≫
      (Scheme.Modules.pullbackComp j (f ⁻¹ᵁ U).ι).app _ ≪≫ eqToIso (by rw [hj])
  have := MMP.Mori.isInvertible_pullback_obj g A.divisorialSheaf
  exact Scheme.Modules.isAmple_of_iso e h2

/-- On an integral normal scheme, the pull-back of the invertible sheaf of a Cartier divisor along
any morphism is the invertible sheaf of a Cartier divisor: the divisor of the pulled-back local
frame. -/
private theorem exists_isCartier_divisorialSheaf_iso_pullback {V W : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] (u : V ⟶ W) {B : Divisor W} (hB : B.IsCartier) :
    ∃ Δ : Divisor V, Δ.IsCartier ∧
      Nonempty (Δ.divisorialSheaf ≅ (Scheme.Modules.pullback u).obj B.divisorialSheaf) := by
  let F := pullbackFrame u hB
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

end Ample

section Generic

open MvPolynomial

/-- **Choosing the first block of a general point.** If `P` is a nonzero polynomial in the
coefficients of `m + 1` linear forms and `Q` a nonzero polynomial in the coefficients of one form,
there is a first form `x` with `Q(x) ≠ 0` such that `P(x, ·)` is a nonzero polynomial `P'` in the
remaining `m` forms. -/
private theorem exists_eval_ne_zero_and_cons {K : Type*} [Field K] [Infinite K] {σ : Type*}
    {m : ℕ} {P : MvPolynomial (Fin (m + 1) × σ) K} (hP : P ≠ 0) {Q : MvPolynomial σ K}
    (hQ : Q ≠ 0) :
    ∃ x : σ → K, eval x Q ≠ 0 ∧ ∃ P' : MvPolynomial (Fin m × σ) K, P' ≠ 0 ∧
      ∀ y : Fin m → σ → K, eval (fun p => y p.1 p.2) P' =
        eval (fun p => (Fin.cons x y : Fin (m + 1) → σ → K) p.1 p.2) P := by
  classical
  -- substitution of `x` in the first block
  let sub : (σ → K) → Fin (m + 1) × σ → MvPolynomial (Fin m × σ) K := fun x p =>
    Fin.cases (C (x p.2)) (fun i => X (i, p.2)) p.1
  have hsub : ∀ (x : σ → K) (y : Fin m → σ → K),
      eval (fun p => y p.1 p.2) (bind₁ (sub x) P) =
        eval (fun p => (Fin.cons x y : Fin (m + 1) → σ → K) p.1 p.2) P := by
    intro x y
    change eval₂Hom (RingHom.id K) _ (bind₁ (sub x) P) = eval₂Hom (RingHom.id K) _ P
    rw [eval₂Hom_bind₁]
    congr 2
    funext ⟨i, s⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [sub]
    · simp [sub]
  by_contra! H
  have hvan : ∀ x : σ → K, eval x Q ≠ 0 → bind₁ (sub x) P = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨y, hy⟩ := H x hx _ h0
    exact hy (hsub x y)
  -- `Q` (in the first block) times `P` vanishes identically
  let Q₀ : MvPolynomial (Fin (m + 1) × σ) K := rename (fun s => ((0 : Fin (m + 1)), s)) Q
  have hQ₀ : Q₀ ≠ 0 := by
    intro h
    apply hQ
    refine rename_injective (fun s => ((0 : Fin (m + 1)), s))
      (fun a b (hab : ((0 : Fin (m + 1)), a) = (0, b)) => (Prod.mk.inj hab).2) ?_
    rw [map_zero]; exact h
  have hzero : Q₀ * P = 0 := by
    refine funext fun c => ?_
    rw [map_mul, map_zero]
    let x : σ → K := fun s => c (0, s)
    have hQx : eval c Q₀ = eval x Q := by
      simp only [Q₀, eval_rename]; rfl
    by_cases hx : eval x Q = 0
    · rw [hQx, hx, zero_mul]
    · have h1 := hsub x (fun i s => c (i.succ, s))
      have h2 : (fun p : Fin (m + 1) × σ =>
          (Fin.cons x (fun i s => c (i.succ, s)) : Fin (m + 1) → σ → K) p.1 p.2) = c := by
        funext ⟨i, s⟩
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [hvan x hx, map_zero, h2] at h1
      rw [← h1, mul_zero]
  exact (mul_ne_zero hQ₀ hP) hzero

end Generic

section Subscheme

open Scheme.IdealSheafData

/-- Inside the closed subscheme of `I`, the preimage of a closed subscheme `K ⊇ V(I)`... the
ideal `K ≥ I` is recovered from its restriction to `V(I)`: `(K|_{V(I)})` pushed forward is `K`. -/
private theorem map_comap_subschemeι_of_le {X : Scheme.{0}} {I K : X.IdealSheafData}
    (h : I ≤ K) : (K.comap I.subschemeι).map I.subschemeι = K := by
  have hK : inclusion h ≫ I.subschemeι = K.subschemeι := inclusion_subschemeι h
  have hsnd : IsIso (Limits.pullback.snd I.subschemeι K.subschemeι) := by
    have := (inferInstance :
      IsIso (Limits.pullback.snd I.subschemeι (inclusion h ≫ I.subschemeι)))
    rwa [hK] at this
  rw [Scheme.IdealSheafData.map, ← comapIso_hom_fst, Category.assoc, Scheme.Hom.ker_comp_of_isIso,
    Limits.pullback.condition, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

/-- The preimage of `I` in its own closed subscheme is everything. -/
private theorem comap_self_subschemeι {X : Scheme.{0}} (I : X.IdealSheafData) :
    I.comap I.subschemeι = ⊥ :=
  Scheme.Hom.ker_eq_bot_of_isIso _

/-- The closed subscheme `V(J) ∩ V(I)`, cut out by `J` inside `V(I)`, is the closed subscheme of
`I ⊔ J`, compatibly with the immersions into `X`. -/
private theorem exists_iso_comap_subschemeι {X : Scheme.{0}} (I J : X.IdealSheafData) :
    ∃ e : (J.comap I.subschemeι).subscheme ≅ (I ⊔ J).subscheme,
      e.hom ≫ (I ⊔ J).subschemeι = (J.comap I.subschemeι).subschemeι ≫ I.subschemeι := by
  have hker : ((J.comap I.subschemeι).subschemeι ≫ I.subschemeι).ker = I ⊔ J := by
    have h1 : (I ⊔ J).comap I.subschemeι = J.comap I.subschemeι := by
      rw [comap_sup, comap_self_subschemeι, bot_sup_eq]
    rw [← h1]
    exact map_comap_subschemeι_of_le le_sup_left
  set f := (J.comap I.subschemeι).subschemeι ≫ I.subschemeι with hf
  let e₂ : f.image ≅ (I ⊔ J).subscheme :=
    { hom := inclusion hker.ge
      inv := inclusion hker.le
      hom_inv_id := by rw [inclusion_comp, inclusion_id]
      inv_hom_id := by rw [inclusion_comp, inclusion_id] }
  refine ⟨asIso f.toImage ≪≫ e₂, ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Category.assoc, e₂, inclusion_subschemeι]
  exact f.toImage_imageι

/-- For a closed immersion `f` with kernel contained in `K`, the ideal `K` is recovered from its
restriction along `f`. -/
private theorem map_comap_of_isClosedImmersion {X Y : Scheme.{0}} (f : Y ⟶ X)
    [IsClosedImmersion f] {K : X.IdealSheafData} (h : f.ker ≤ K) : (K.comap f).map f = K := by
  have hK : IsClosedImmersion.lift f K.subschemeι (by rwa [ker_subschemeι]) ≫ f = K.subschemeι :=
    IsClosedImmersion.lift_fac _ _ _
  have hsnd : IsIso (Limits.pullback.snd f K.subschemeι) := by
    have := (inferInstance : IsIso (Limits.pullback.snd f
      (IsClosedImmersion.lift f K.subschemeι (by rwa [ker_subschemeι]) ≫ f)))
    rwa [hK] at this
  rw [Scheme.IdealSheafData.map, ← comapIso_hom_fst, Category.assoc, Scheme.Hom.ker_comp_of_isIso,
    Limits.pullback.condition, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

/-- The preimage of the kernel of a closed immersion along it is everything. -/
private theorem comap_ker_of_isClosedImmersion {X Y : Scheme.{0}} (f : Y ⟶ X)
    [IsClosedImmersion f] : f.ker.comap f = ⊥ := by
  have hf : f.toImage ≫ f.ker.subschemeι = f := f.toImage_imageι
  have : IsIso (Limits.pullback.fst f f.ker.subschemeι) := by
    have := (inferInstance : IsIso (Limits.pullback.fst (f.toImage ≫ f.ker.subschemeι)
      f.ker.subschemeι))
    rwa [hf] at this
  exact Scheme.Hom.ker_eq_bot_of_isIso _

/-- The kernel of `g ≫ f`, for a closed immersion `f`, when `g` cuts out `J` pulled back along
`f`. -/
private theorem ker_comp_of_isClosedImmersion {X Y Z : Scheme.{0}} (f : Y ⟶ X)
    [IsClosedImmersion f] (J : X.IdealSheafData) (g : Z ⟶ Y) (hg : g.ker = J.comap f) :
    (g ≫ f).ker = f.ker ⊔ J := by
  rw [Scheme.Hom.ker_comp, hg]
  have h1 : (f.ker ⊔ J).comap f = J.comap f := by
    rw [comap_sup, comap_ker_of_isClosedImmersion, bot_sup_eq]
  rw [← h1]
  exact map_comap_of_isClosedImmersion f le_sup_left

end Subscheme

section Cut

open MMP.Threefold.Bridges MonoidalCategory
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **One general hyperplane section of a smooth variety.** Let `W` be a smooth variety over `ℂ`
of dimension `d + 2` with a locally quasi-finite morphism `ψ : W ⟶ ℙᴷ`. For `[c]` in a dense open
of the dual projective space, `W' = ψ⁻¹(H_c)` is empty or a smooth variety of dimension `d + 1`
whose canonical sheaf is `ι^*(ω_W ⊗ ψ^*𝒪(1))` (adjunction). -/
private theorem exists_dense_open_cut {W : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sW] [Smooth sW] {d : ℕ}
    (hdim : topologicalKrullDim W = (d + 2 : ℕ)) {K : ℕ} (ψ : W ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K))
    (hψ : ψ ≫ Stacks.ProjectiveCohomology.projModelToSpec ℂ K = sW) [LocallyQuasiFinite ψ] :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K)).Opens, Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K))) ∧
      ∀ (c : Fin (K + 1) → ℂ) (hc : c ≠ 0), dualPoint c hc ∈ U →
        ((hyperplaneSection ψ c).support : Set W).Nonempty →
        ∃ (W' : Scheme.{0}) (ι : W' ⟶ W) (_ : IsClosedImmersion ι),
          ι.ker = hyperplaneSection ψ c ∧ AlgebraicGeometry.IsVariety ℂ (ι ≫ sW) ∧
          Smooth (ι ≫ sW) ∧ topologicalKrullDim W' = (d + 1 : ℕ) ∧
          Nonempty (Scheme.Hom.relativeDifferentialForms (ι ≫ sW) (d + 1) ≅
            (Scheme.Modules.pullback ι).obj (Scheme.Hom.relativeDifferentialForms sW (d + 2) ⊗
              (Scheme.Modules.pullback ψ).obj (twistOne ℂ K))) := by
  letI : W.Over (Spec (.of ℂ)) := ⟨sW⟩
  have hsW : W ↘ Spec (.of ℂ) = sW := rfl
  have hsm : IsSmoothScheme sW := by
    rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, Scheme.Hom.smoothLocus_eq_top_iff]
    infer_instance
  obtain ⟨hWn, hWn'⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm
  haveI := hWn
  haveI := hWn'
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  obtain ⟨KW, hKW⟩ := exists_isCanonicalDivisor_of_isSmoothScheme sW hsm hdim
  have hpair : MMP.Mori.IsPair (W ↘ Spec (.of ℂ)) 0 :=
    ⟨⟨(inferInstance : AlgebraicGeometry.IsVariety ℂ sW), hWn'⟩, d + 2, KW, hKW, by
      rw [add_zero]; exact MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  have hdim2 : (2 : WithBot ℕ∞) ≤ topologicalKrullDim W := by rw [hdim]; exact_mod_cast (by omega)
  obtain ⟨U₁, hU₁, hadj⟩ := MMP.Mori.IsPair.exists_dense_open_adjunction_connectedComponent_zeroScheme
    hpair hdim2 (pulledSystem ψ) (iSup_nonvanishingOpen_pulledSystem hψ)
  haveI : AlgebraicGeometry.IsVariety ℂ (W ↘ Spec (.of ℂ)) := ‹AlgebraicGeometry.IsVariety ℂ sW›
  obtain ⟨⟨U₂, hU₂, hgen⟩, -⟩ := exists_dense_open_hyperplaneSection ℂ (V := W) ψ hψ
    (fun _ : Unit => (Set.univ : Set W)) (fun _ => isClosed_univ)
    (fun _ => IrreducibleSpace.isIrreducible_univ W) (fun e : Empty => e.elim)
    (fun e => e.elim) 0
  -- the image of `ψ` has the dimension of `W`
  have hrange : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure (Set.range ψ)) := by
    have h := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range ψ ℂ sW
      (Stacks.ProjectiveCohomology.projModelToSpec ℂ K) hψ
    have hfib : topologicalKrullDim (ψ.fiber (ψ (genericPoint W))) ≤ 0 := by
      have : DiscreteTopology (ψ.fiber (ψ (genericPoint W))) :=
        (IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mp inferInstance).2
      exact topologicalKrullDim_zero_of_discreteTopology _
    rw [hdim] at h
    by_contra hlt
    push Not at hlt
    have h1 : topologicalKrullDim (closure (Set.range ψ)) ≤ 1 := by
      generalize topologicalKrullDim (closure (Set.range ψ)) = b at hlt ⊢
      cases b using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe e =>
        cases e using ENat.recTopCoe with
        | top => exact absurd hlt (by decide)
        | coe n =>
          have h' : ((n : ℕ∞) : WithBot ℕ∞) < ((2 : ℕ∞) : WithBot ℕ∞) := hlt
          have h'' : (n : ℕ∞) < 2 := WithBot.coe_lt_coe.mp h'
          have : n < 2 := by exact_mod_cast h''
          have h3 : (n : ℕ∞) ≤ 1 := by exact_mod_cast (by omega : n ≤ 1)
          exact WithBot.coe_le_coe.mpr h3
    have h2 : ((d + 2 : ℕ) : WithBot ℕ∞) ≤ 0 + 1 := by
      calc ((d + 2 : ℕ) : WithBot ℕ∞) = _ := h
        _ ≤ 0 + 1 := add_le_add hfib h1
    have h3 : ((d + 2 : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
      simpa using h2
    have h4 : d + 2 ≤ 1 := by exact_mod_cast h3
    omega
  refine ⟨U₁ ⊓ U₂, ?_, fun c hc hmem hne => ?_⟩
  · rw [Opens.coe_inf]
    exact hU₁.inter_of_isOpen_left hU₂ U₁.isOpen
  obtain ⟨hsmZ, hirrZ, hZl⟩ := hgen c hc hmem.2
  obtain ⟨hnot, -, hpure, -⟩ := hZl ()
  have hZ : Stacks.Divisors.zeroScheme W (pullTwist ψ) (systemSection (pulledSystem ψ) c) =
      hyperplaneSection ψ c := zeroScheme_pulledSystem hψ c
  set Z' := Stacks.Divisors.zeroScheme W (pullTwist ψ) (systemSection (pulledSystem ψ) c)
    with hZ'def
  have hirr : IsIrreducible ((hyperplaneSection ψ c).support : Set W) := hirrZ hrange
  have hsmZ' : Smooth ((hyperplaneSection ψ c).subschemeι ≫ sW) :=
    hsmZ (inferInstance : Smooth sW)
  -- the dimension of the cut
  have huniv : topologicalKrullDim (Set.univ : Set W) = topologicalKrullDim W :=
    (Homeomorph.Set.univ W).isHomeomorph.topologicalKrullDim_eq
  have hnsub : ¬ (ψ '' (Set.univ : Set W)).Subsingleton := by
    intro hsub
    obtain ⟨w, -⟩ := hne
    have hpre : ψ ⁻¹' {ψ w} = (Set.univ : Set W) := by
      ext x
      simp only [Set.mem_univ, Set.mem_preimage, Set.mem_singleton_iff, iff_true]
      exact hsub ⟨x, trivial, rfl⟩ ⟨w, trivial, rfl⟩
    have hdisc := (ψ.isDiscrete_preimage_singleton (ψ w)).to_subtype
    rw [hpre] at hdisc
    have h0 := topologicalKrullDim_zero_of_discreteTopology (Set.univ : Set W)
    rw [huniv, hdim] at h0
    have : d + 2 ≤ 0 := by exact_mod_cast h0
    omega
  have hdimS : topologicalKrullDim ((hyperplaneSection ψ c).support : Set W) + 1 =
      topologicalKrullDim (Set.univ : Set W) := by
    refine hpure hnsub _ ⟨⟨hirr, fun x hx => ⟨Set.mem_univ x, hx⟩⟩, fun T hT hST => ?_⟩
    exact fun x hx => (hT.2 hx).2
  have hdimS' : topologicalKrullDim ((hyperplaneSection ψ c).support : Set W) = (d + 1 : ℕ) := by
    rw [huniv, hdim] at hdimS
    generalize topologicalKrullDim ((hyperplaneSection ψ c).support : Set W) = b at hdimS ⊢
    cases b using WithBot.recBotCoe with
    | bot =>
      exfalso
      have h1 : ((⊥ : WithBot ℕ∞) + 1) = ⊥ := WithBot.bot_add 1
      rw [h1] at hdimS
      exact WithBot.bot_ne_coe hdimS
    | coe e =>
      cases e using ENat.recTopCoe with
      | top =>
        exfalso
        have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
        rw [h1] at hdimS
        exact ENat.top_ne_coe (d + 2) (WithBot.coe_eq_coe.mp hdimS)
      | coe n =>
        have h1 : ((n + 1 : ℕ) : WithBot ℕ∞) = ((d + 2 : ℕ) : WithBot ℕ∞) := by
          rw [← hdimS]; push_cast; rfl
        have : n + 1 = d + 2 := by exact_mod_cast h1
        have : n = d + 1 := by omega
        subst this
        rfl
  -- the general member, as the open `⊤` of the zero scheme
  have hconn : _root_.IsConnected ((⊤ : Z'.subscheme.Opens) : Set Z'.subscheme) := by
    have hconnS : _root_.IsConnected (Set.range Z'.subschemeι) := by
      rw [Scheme.IdealSheafData.range_subschemeι, hZ]
      exact hirr.isConnected
    haveI : ConnectedSpace (Set.range Z'.subschemeι) := isConnected_iff_connectedSpace.mp hconnS
    let e := Z'.subschemeι.isEmbedding.toHomeomorph
    haveI : ConnectedSpace Z'.subscheme := e.symm.surjective.connectedSpace e.symm.continuous
    exact isConnected_univ
  obtain ⟨hWv, -, hK⟩ := hadj c hc hmem.1 ⊤ isClopen_univ hconn
  set ι : (⊤ : Z'.subscheme.Opens).toScheme ⟶ W := (⊤ : Z'.subscheme.Opens).ι ≫ Z'.subschemeι
    with hιdef
  haveI : IsIso (⊤ : Z'.subscheme.Opens).ι := by
    rw [← Scheme.topIso_hom]; infer_instance
  have hιvar : AlgebraicGeometry.IsVariety ℂ (ι ≫ sW) := hWv.1
  haveI : Smooth (Z'.subschemeι ≫ sW) := by rw [hZ]; exact hsmZ'
  haveI : Smooth (ι ≫ sW) := by rw [hιdef, Category.assoc]; infer_instance
  have hdimW' : topologicalKrullDim (⊤ : Z'.subscheme.Opens).toScheme = (d + 1 : ℕ) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (⊤ : Z'.subscheme.Opens).ι)).isHomeomorph,
      MMP.Mori.topologicalKrullDim_subscheme_eq, hZ]
    exact hdimS'
  refine ⟨_, ι, inferInstance, ?_, hιvar, inferInstance, hdimW', ?_⟩
  · rw [hιdef, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι, hZ]
  -- the adjunction isomorphism
  haveI : IsLocallyNoetherian (⊤ : Z'.subscheme.Opens).toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sW)
  haveI : IsNormal (⊤ : Z'.subscheme.Opens).toScheme := hWv.2
  haveI : CompactSpace (⊤ : Z'.subscheme.Opens).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (ι ≫ sW)
  have hιs : ι ≫ sW = (⊤ : Z'.subscheme.Opens).ι ≫ Z'.subschemeι ≫ W ↘ Spec (.of ℂ) := by
    rw [hιdef, Category.assoc, hsW]
  haveI : IsIntegral (⊤ : Z'.subscheme.Opens).toScheme := hιvar.toIsIntegral
  haveI : AlgebraicGeometry.IsVariety ℂ
      ((⊤ : Z'.subscheme.Opens).ι ≫ Z'.subschemeι ≫ W ↘ Spec (.of ℂ)) := hιs ▸ hιvar
  haveI : Smooth ((⊤ : Z'.subscheme.Opens).ι ≫ Z'.subschemeι ≫ W ↘ Spec (.of ℂ)) :=
    hιs ▸ inferInstance
  have hsm' : IsSmoothScheme ((⊤ : Z'.subscheme.Opens).ι ≫ Z'.subschemeι ≫ W ↘ Spec (.of ℂ)) := by
    rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, Scheme.Hom.smoothLocus_eq_top_iff]
    infer_instance
  obtain ⟨K', hK'⟩ := exists_isCanonicalDivisor_of_isSmoothScheme _ hsm' hdimW'
  have hKWc : KW.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm KW
  obtain ⟨D', hD', -, ⟨eD'⟩⟩ := hK 1 one_pos (d + 2) (d + 1) KW K' hKW hK' KW (by simp) hKWc
  have h0 : DivisorWithCoeffs.restrictComponents
      ((⊤ : Z'.subscheme.Opens).ι ≫ Z'.subschemeι) (0 : QDivisor W) = 0 := by
    have hz : DivisorWithCoeffs.restrictComponentsCoeff
        ((⊤ : Z'.subscheme.Opens).ι ≫ Z'.subschemeι) (0 : QDivisor W) = 0 := by
      funext C
      simp [DivisorWithCoeffs.restrictComponentsCoeff]
    have hfin : (Function.support (DivisorWithCoeffs.restrictComponentsCoeff
        ((⊤ : Z'.subscheme.Opens).ι ≫ Z'.subschemeι) (0 : QDivisor W))).Finite := by
      rw [hz, Function.support_zero]; exact Set.finite_empty
    ext C
    rw [DivisorWithCoeffs.coeff_restrictComponents
      ((⊤ : Z'.subscheme.Opens).ι ≫ Z'.subschemeι) hfin C]
    simp [DivisorWithCoeffs.coeff]
  have hD'K' : D' = K' := by
    apply Divisor.toQDivisor_injective
    rw [hD', h0, add_zero, Nat.cast_one, one_smul]
  subst hD'K'
  obtain ⟨e₁⟩ := MMP.Mori.nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hsm' hK'
  obtain ⟨e₂⟩ := MMP.Mori.nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hsm hKW
  have e₃ : MMP.Intersection.Scheme.Modules.tensorPow (pullTwist ψ) 1 ≅ pullTwist ψ :=
    λ_ (pullTwist ψ)
  refine ⟨?_⟩
  rw [hιs]
  refine eqToIso ?_ ≪≫ e₁.symm ≪≫ eD' ≪≫ (Scheme.Modules.pullback _).mapIso (e₂ ⊗ᵢ e₃) ≪≫
    eqToIso ?_
  · push_cast; rfl
  · push_cast; rfl

/-- The degree of the differentials of a curve `ι : C ⟶ W` whose top forms are `ι^*(M ⊗ L)`. -/
private theorem invertibleCurveDegree_relativeDifferentials_eq_of_iso {C W : Scheme.{0}}
    (ι : C ⟶ W) (sW : W ⟶ Spec (.of ℂ)) [IsProper (ι ≫ sW)] (hC : topologicalKrullDim C ≤ 1)
    {M L : W.Modules} [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (Scheme.Hom.relativeDifferentials (ι ≫ sW))]
    (e : Scheme.Hom.relativeDifferentialForms (ι ≫ sW) 1 ≅ (Scheme.Modules.pullback ι).obj (M ⊗ L)) :
    invertibleCurveDegree ℂ (ι ≫ sW) hC (Scheme.Hom.relativeDifferentials (ι ≫ sW)) =
      degreeOn ℂ sW ι hC M + degreeOn ℂ sW ι hC L := by
  haveI hML : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨W.toRingedSpace.presheaf,
        W.toRingedSpace.IsSheaf⟩).obj M).obj L) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible W.presheaf W.ringCatSheaf.2 _ _
  haveI : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (M ⊗ L : W.Modules) := hML
  haveI := MMP.Mori.isInvertible_pullback_obj ι (M ⊗ L : W.Modules)
  rw [invertibleCurveDegree_eq_of_iso ℂ (ι ≫ sW) hC
    ((Scheme.Modules.exteriorPowerOneIsoSelf _).symm ≪≫ e)]
  exact degreeOn_tensorSheaf ℂ sW ι hC M L

/-- The degree of the differentials of a proper curve depends only on the structure morphism,
not on how it is written. -/
private theorem invertibleCurveDegree_relativeDifferentials_congr {C : Scheme.{0}}
    {f g : C ⟶ Spec (.of ℂ)} (h : f = g) [IsProper f] [IsProper g]
    {hC : topologicalKrullDim C ≤ 1}
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 (Scheme.Hom.relativeDifferentials f)]
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 (Scheme.Hom.relativeDifferentials g)] :
    invertibleCurveDegree ℂ f hC (Scheme.Hom.relativeDifferentials f) =
      invertibleCurveDegree ℂ g hC (Scheme.Hom.relativeDifferentials g) := by
  subst h
  rfl

/-- The supremum over `Fin (m + 1)` of a family `F ∘ Fin.cons x c` splits off the first term. -/
private theorem iSup_fin_cons {α β : Type*} [CompleteLattice α] {m : ℕ} (F : β → α) (x : β)
    (c : Fin m → β) :
    (⨆ j, F ((Fin.cons x c : Fin (m + 1) → β) j)) = F x ⊔ ⨆ j, F (c j) := by
  refine le_antisymm (iSup_le fun j => ?_)
    (sup_le (le_iSup_of_le 0 (by rw [Fin.cons_zero]))
      (iSup_le fun i => le_iSup_of_le i.succ (by rw [Fin.cons_succ])))
  cases j using Fin.cases with
  | zero => rw [Fin.cons_zero]; exact le_sup_left
  | succ i => rw [Fin.cons_succ]; exact le_sup_of_le_right (le_iSup_of_le i le_rfl)

/-- The hyperplane sections of `g ≫ χ` are the preimages of those of `χ`, compatibly with
suprema. -/
private theorem iSup_hyperplaneSection_comp {Y Y' : Scheme.{0}} (g : Y' ⟶ Y) {K m : ℕ}
    (χ : Y ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K)) (c : Fin m → Fin (K + 1) → ℂ) :
    (⨆ j, hyperplaneSection (g ≫ χ) (c j)) = (⨆ j, hyperplaneSection χ (c j)).comap g := by
  rw [(Scheme.IdealSheafData.map_gc g).l_iSup]
  exact iSup_congr fun j => by simp only [hyperplaneSection, Scheme.IdealSheafData.comap_comp]

/-- **Bertini for reducedness**, for the hyperplane sections of a morphism to `ℙᴷ`: on a reduced
scheme of finite type over `ℂ`, the sections by the hyperplanes off a hypersurface of the dual
space are reduced. -/
private theorem exists_polynomial_isReduced_hyperplaneSection {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [IsReduced Y] [LocallyOfFiniteType sY] [QuasiCompact sY] {K : ℕ}
    (χ : Y ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K))
    (hχ : χ ≫ Stacks.ProjectiveCohomology.projModelToSpec ℂ K = sY) :
    ∃ Q : MvPolynomial (Fin (K + 1)) ℂ, Q ≠ 0 ∧ ∀ c : Fin (K + 1) → ℂ,
      MvPolynomial.eval c Q ≠ 0 → IsReduced (hyperplaneSection χ c).subscheme := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sY›
  haveI : QuasiCompact (Y ↘ Spec (.of ℂ)) := ‹QuasiCompact sY›
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_isReduced_zeroScheme (pulledSystem χ)
    (iSup_nonvanishingOpen_pulledSystem hχ)
  exact ⟨Q, hQ0, fun c hc => zeroScheme_pulledSystem hχ c ▸ hQ c hc⟩

/-- `V(J) ∩ V(I)` is reduced when the cut of `V(I)` by `J` is. -/
private theorem isReduced_sup_of_isReduced_comap {Y : Scheme.{0}} (I J : Y.IdealSheafData)
    (h : IsReduced (J.comap I.subschemeι).subscheme) : IsReduced (I ⊔ J).subscheme := by
  obtain ⟨e, -⟩ := exists_iso_comap_subschemeι I J
  exact isReduced_of_isOpenImmersion e.inv

/-- A nonzero polynomial over an infinite field has a non-root, in the block coordinates. -/
private theorem exists_eval_block_ne_zero {m K : ℕ}
    {P : MvPolynomial (Fin m × Fin (K + 1)) ℂ} (hP : P ≠ 0) :
    ∃ c : Fin m → Fin (K + 1) → ℂ, MvPolynomial.eval (fun p => c p.1 p.2) P ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hP (MvPolynomial.funext fun y => by rw [map_zero]; exact hcon (fun i k => y (i, k)))

/-- **General complete intersections of a reduced scheme are reduced.** For a reduced scheme `Y`
of finite type over `ℂ` with a morphism `χ : Y ⟶ ℙᴷ` and a nonzero polynomial `P` in the
coefficients of `m + 1` linear forms, some forms `c` with `P(c) ≠ 0` cut out a reduced
`χ⁻¹(H_{c₀} ∩ ⋯ ∩ H_{c_m})`; the forms are chosen one at a time. -/
private theorem exists_isReduced_completeIntersection (m : ℕ) :
    ∀ {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsReduced Y] [LocallyOfFiniteType sY]
      [QuasiCompact sY] {K : ℕ} (χ : Y ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K))
      (_ : χ ≫ Stacks.ProjectiveCohomology.projModelToSpec ℂ K = sY)
      (P : MvPolynomial (Fin (m + 1) × Fin (K + 1)) ℂ), P ≠ 0 →
      ∃ c : Fin (m + 1) → Fin (K + 1) → ℂ, MvPolynomial.eval (fun p => c p.1 p.2) P ≠ 0 ∧
        IsReduced (⨆ j, hyperplaneSection χ (c j)).subscheme := by
  induction m with
  | zero =>
    intro Y sY _ _ _ K χ hχ P hP
    obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_isReduced_hyperplaneSection sY χ hχ
    obtain ⟨x, hx, P', hP', hP'eq⟩ := exists_eval_ne_zero_and_cons hP hQ0
    obtain ⟨c', hc'⟩ := exists_eval_block_ne_zero hP'
    refine ⟨Fin.cons x c', by rw [← hP'eq c']; exact hc', ?_⟩
    rw [iSup_fin_cons (hyperplaneSection χ) x c', iSup_of_empty, sup_bot_eq]
    exact hQ x hx
  | succ m ih =>
    intro Y sY _ _ _ K χ hχ P hP
    obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_isReduced_hyperplaneSection sY χ hχ
    obtain ⟨x, hx, P', hP', hP'eq⟩ := exists_eval_ne_zero_and_cons hP hQ0
    haveI : IsReduced (hyperplaneSection χ x).subscheme := hQ x hx
    obtain ⟨c', hc'P, hc'⟩ := ih ((hyperplaneSection χ x).subschemeι ≫ sY)
      ((hyperplaneSection χ x).subschemeι ≫ χ) (by rw [Category.assoc, hχ]) P' hP'
    refine ⟨Fin.cons x c', by rw [← hP'eq c']; exact hc'P, ?_⟩
    rw [iSup_fin_cons (hyperplaneSection χ) x c']
    rw [iSup_hyperplaneSection_comp] at hc'
    exact isReduced_sup_of_isReduced_comap _ _ hc'

/-- **A general complete intersection curve of a smooth variety and its canonical degree.**
Let `W` be a smooth variety of dimension `d + 2` over `ℂ` with a locally quasi-finite morphism
`ψ : W ⟶ ℙᴷ`, and `P` a nonzero polynomial in the coefficients of `d + 1` linear forms. There are
forms `c` with `P(c) ≠ 0` such that `C = ψ⁻¹(H_{c₀} ∩ ⋯ ∩ H_{c_d})` is empty or a smooth curve
with `deg Ω_C = deg_C ω_W + (d + 1) · deg_C ψ^*𝒪(1)` (adjunction). The forms are chosen one at a
time, `hpoly` turning each Bertini condition into the non-vanishing of a polynomial. -/
private theorem exists_completeIntersection_curve
    (hpoly : ∀ {K : ℕ} (U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K)).Opens),
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K))) →
      ∃ Q : MvPolynomial (Fin (K + 1)) ℂ, Q ≠ 0 ∧
        ∀ (c : Fin (K + 1) → ℂ) (hc : c ≠ 0), MvPolynomial.eval c Q ≠ 0 → dualPoint c hc ∈ U)
    (d : ℕ) :
    ∀ {W : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsVariety ℂ sW] [Smooth sW]
      (hdim : topologicalKrullDim W = (d + 2 : ℕ)) {K : ℕ} (ψ : W ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K))
      (_ : ψ ≫ Stacks.ProjectiveCohomology.projModelToSpec ℂ K = sW) [LocallyQuasiFinite ψ]
      {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsReduced Y] [LocallyOfFiniteType sY]
      [QuasiCompact sY] (χ : Y ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K))
      (_ : χ ≫ Stacks.ProjectiveCohomology.projModelToSpec ℂ K = sY)
      (P : MvPolynomial (Fin (d + 1) × Fin (K + 1)) ℂ), P ≠ 0 →
      ∃ c : Fin (d + 1) → Fin (K + 1) → ℂ, MvPolynomial.eval (fun p => c p.1 p.2) P ≠ 0 ∧
        IsReduced (⨆ j, hyperplaneSection χ (c j)).subscheme ∧
        (((⨆ j, hyperplaneSection ψ (c j)).support : Set W).Nonempty →
          ∃ (C : Scheme.{0}) (ι : C ⟶ W) (_ : IsClosedImmersion ι)
            (_ : AlgebraicGeometry.IsVariety ℂ (ι ≫ sW)) (_ : Smooth (ι ≫ sW))
            (hC : topologicalKrullDim C = 1),
            ι.ker = ⨆ j, hyperplaneSection ψ (c j) ∧
            ∀ (hprop : IsProper (ι ≫ sW)),
              haveI := hprop
              haveI : AlgebraicGeometry.IsCurve ℂ (ι ≫ sW) :=
                { topologicalKrullDim_eq_one := hC }
              haveI := isInvertible_relativeDifferentials_of_isCurve (k := ℂ) (ι ≫ sW)
              haveI := MMP.Intersection.smoothOfRelativeDimension_of_isVariety sW (d + 2) hdim
              haveI := Stacks.Discriminant.isInvertible_relativeDifferentialForms sW (d + 2)
              haveI := MMP.Mori.isInvertible_pullback_obj ψ (twistOne ℂ K)
              invertibleCurveDegree ℂ (ι ≫ sW) hC.le
                  (Scheme.Hom.relativeDifferentials (ι ≫ sW)) =
                degreeOn ℂ sW ι hC.le
                    (Scheme.Hom.relativeDifferentialForms sW ((d + 2 : ℕ) : ℤ)) +
                  ((d + 1 : ℕ) : ℤ) *
                    degreeOn ℂ sW ι hC.le ((Scheme.Modules.pullback ψ).obj (twistOne ℂ K))) := by
  induction d with
  | zero =>
    intro W sW _ _ hdim K ψ hψ _ Y sY _ _ _ χ hχ P hP
    obtain ⟨U, hU, hcut⟩ := exists_dense_open_cut sW (d := 0) hdim ψ hψ
    obtain ⟨Q, hQ0, hQ⟩ := hpoly U hU
    obtain ⟨Qr, hQr0, hQr⟩ := exists_polynomial_isReduced_hyperplaneSection sY χ hχ
    obtain ⟨x, hx, P', hP', hP'eq⟩ := exists_eval_ne_zero_and_cons hP
      (mul_ne_zero (mul_ne_zero hQ0 hQr0) (MvPolynomial.X_ne_zero (0 : Fin (K + 1))))
    rw [map_mul, map_mul, MvPolynomial.eval_X] at hx
    have hx0 : x ≠ 0 := fun h => by simp [h] at hx
    have hxU : dualPoint x hx0 ∈ U := hQ x hx0 (left_ne_zero_of_mul (left_ne_zero_of_mul hx))
    have hxr := hQr x (right_ne_zero_of_mul (left_ne_zero_of_mul hx))
    have hsup : ∀ {T : Scheme.{0}} (τ : T ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K)), (⨆ j, hyperplaneSection τ
        ((Fin.cons x Fin.elim0 : Fin (0 + 1) → Fin (K + 1) → ℂ) j)) = hyperplaneSection τ x :=
      fun τ => by rw [iSup_fin_cons (hyperplaneSection τ) x Fin.elim0, iSup_of_empty, sup_bot_eq]
    refine ⟨Fin.cons x Fin.elim0, ?_, by rw [hsup]; exact hxr, fun hne => ?_⟩
    · rw [← hP'eq Fin.elim0]
      intro h0
      apply hP'
      refine MvPolynomial.funext fun y => ?_
      have : y = fun p => (Fin.elim0 p.1 : Fin (K + 1) → ℂ) p.2 := funext fun p => p.1.elim0
      rw [this, h0, map_zero]
    · rw [hsup] at hne ⊢
      obtain ⟨C, ι, hι, hker, hvar, hsm, hdimC, ⟨eω⟩⟩ := hcut x hx0 hxU hne
      refine ⟨C, ι, hι, hvar, hsm, by simpa using hdimC, hker, fun hprop => ?_⟩
      haveI := hprop
      haveI : AlgebraicGeometry.IsCurve ℂ (ι ≫ sW) :=
        { topologicalKrullDim_eq_one := by simpa using hdimC }
      haveI := isInvertible_relativeDifferentials_of_isCurve (k := ℂ) (ι ≫ sW)
      haveI := MMP.Intersection.smoothOfRelativeDimension_of_isVariety sW (0 + 2) hdim
      haveI := Stacks.Discriminant.isInvertible_relativeDifferentialForms sW (0 + 2)
      haveI := MMP.Mori.isInvertible_pullback_obj ψ (twistOne ℂ K)
      have e : Scheme.Hom.relativeDifferentialForms (ι ≫ sW) 1 ≅ (Scheme.Modules.pullback ι).obj
          (Scheme.Hom.relativeDifferentialForms sW ((0 + 2 : ℕ) : ℤ) ⊗
            (Scheme.Modules.pullback ψ).obj (twistOne ℂ K)) :=
        eqToIso (by norm_num) ≪≫ eω ≪≫ eqToIso (by norm_num)
      rw [invertibleCurveDegree_relativeDifferentials_eq_of_iso ι sW _ e]
      push_cast
      ring
  | succ d ih =>
    intro W sW _ _ hdim K ψ hψ _ Y sY _ _ _ χ hχ P hP
    obtain ⟨U, hU, hcut⟩ := exists_dense_open_cut sW (d := d + 1) hdim ψ hψ
    obtain ⟨Q, hQ0, hQ⟩ := hpoly U hU
    obtain ⟨Qr, hQr0, hQr⟩ := exists_polynomial_isReduced_hyperplaneSection sY χ hχ
    obtain ⟨x, hx, P', hP', hP'eq⟩ := exists_eval_ne_zero_and_cons hP
      (mul_ne_zero (mul_ne_zero hQ0 hQr0) (MvPolynomial.X_ne_zero (0 : Fin (K + 1))))
    rw [map_mul, map_mul, MvPolynomial.eval_X] at hx
    have hx0 : x ≠ 0 := fun h => by simp [h] at hx
    have hxU : dualPoint x hx0 ∈ U := hQ x hx0 (left_ne_zero_of_mul (left_ne_zero_of_mul hx))
    haveI : IsReduced (hyperplaneSection χ x).subscheme :=
      hQr x (right_ne_zero_of_mul (left_ne_zero_of_mul hx))
    have hsup : ∀ c' : Fin (d + 1) → Fin (K + 1) → ℂ,
        (⨆ j, hyperplaneSection ψ ((Fin.cons x c' : Fin (d + 1 + 1) → Fin (K + 1) → ℂ) j)) =
          hyperplaneSection ψ x ⊔ ⨆ j, hyperplaneSection ψ (c' j) :=
      fun c' => iSup_fin_cons (hyperplaneSection ψ) x c'
    have hred : ∀ c' : Fin (d + 1) → Fin (K + 1) → ℂ,
        IsReduced (⨆ j, hyperplaneSection ((hyperplaneSection χ x).subschemeι ≫ χ)
          (c' j)).subscheme →
        IsReduced (⨆ j, hyperplaneSection χ
          ((Fin.cons x c' : Fin (d + 1 + 1) → Fin (K + 1) → ℂ) j)).subscheme := fun c' h => by
      rw [iSup_fin_cons (hyperplaneSection χ) x c']
      rw [iSup_hyperplaneSection_comp] at h
      exact isReduced_sup_of_isReduced_comap _ _ h
    by_cases hne₀ : ((hyperplaneSection ψ x).support : Set W).Nonempty
    · obtain ⟨W', ι₀, hι₀, hker₀, hvar₀, hsm₀, hdim₀, ⟨eω⟩⟩ := hcut x hx0 hxU hne₀
      haveI := hι₀
      haveI := hvar₀
      haveI := hsm₀
      have hdim₀' : topologicalKrullDim W' = (d + 2 : ℕ) := hdim₀
      obtain ⟨c', hc'P, hc'red, hc'⟩ :=
        ih (ι₀ ≫ sW) hdim₀' (ι₀ ≫ ψ) (by rw [Category.assoc, hψ])
          ((hyperplaneSection χ x).subschemeι ≫ sY) ((hyperplaneSection χ x).subschemeι ≫ χ)
          (by rw [Category.assoc, hχ]) P' hP'
      have hJ : (⨆ j, hyperplaneSection (ι₀ ≫ ψ) (c' j)) =
          (⨆ j, hyperplaneSection ψ (c' j)).comap ι₀ := iSup_hyperplaneSection_comp ι₀ ψ c'
      refine ⟨Fin.cons x c', by rw [← hP'eq c']; exact hc'P, hred c' hc'red, fun hne => ?_⟩
      rw [hsup] at hne ⊢
      have hne' : ((⨆ j, hyperplaneSection (ι₀ ≫ ψ) (c' j)).support : Set W').Nonempty := by
        obtain ⟨w, hw⟩ := hne
        rw [Scheme.IdealSheafData.support_sup] at hw
        obtain ⟨h1, h2⟩ := hw
        rw [← hker₀, Scheme.Hom.support_ker] at h1
        rw [ι₀.isClosedEmbedding.isClosed_range.closure_eq] at h1
        obtain ⟨w', rfl⟩ := h1
        refine ⟨w', ?_⟩
        rw [hJ, Scheme.IdealSheafData.support_comap]
        exact h2
      obtain ⟨C, ι', hι', hvar', hsm', hC, hker', hdeg'⟩ := hc' hne'
      haveI := hι'
      haveI hvar'' : AlgebraicGeometry.IsVariety ℂ ((ι' ≫ ι₀) ≫ sW) := by
        rw [Category.assoc]; exact hvar'
      haveI hsm'' : Smooth ((ι' ≫ ι₀) ≫ sW) := by rw [Category.assoc]; exact hsm'
      refine ⟨C, ι' ≫ ι₀, inferInstance, hvar'', hsm'', hC, ?_, fun hprop => ?_⟩
      · rw [ker_comp_of_isClosedImmersion ι₀ _ ι' (by rw [hker', hJ]), hker₀]
      haveI := hprop
      haveI hprop' : IsProper (ι' ≫ ι₀ ≫ sW) := by rw [← Category.assoc]; exact hprop
      have h := hdeg' hprop'
      haveI : AlgebraicGeometry.IsCurve ℂ ((ι' ≫ ι₀) ≫ sW) := { topologicalKrullDim_eq_one := hC }
      haveI : AlgebraicGeometry.IsCurve ℂ (ι' ≫ ι₀ ≫ sW) := { topologicalKrullDim_eq_one := hC }
      haveI := isInvertible_relativeDifferentials_of_isCurve (k := ℂ) ((ι' ≫ ι₀) ≫ sW)
      haveI := isInvertible_relativeDifferentials_of_isCurve (k := ℂ) (ι' ≫ ι₀ ≫ sW)
      haveI := MMP.Intersection.smoothOfRelativeDimension_of_isVariety sW (d + 1 + 2) hdim
      haveI := Stacks.Discriminant.isInvertible_relativeDifferentialForms sW (d + 1 + 2)
      haveI := MMP.Mori.isInvertible_pullback_obj ψ (twistOne ℂ K)
      haveI := MMP.Intersection.smoothOfRelativeDimension_of_isVariety (ι₀ ≫ sW) (d + 2) hdim₀'
      haveI := Stacks.Discriminant.isInvertible_relativeDifferentialForms (ι₀ ≫ sW) (d + 2)
      haveI := MMP.Mori.isInvertible_pullback_obj (ι₀ ≫ ψ) (twistOne ℂ K)
      rw [invertibleCurveDegree_relativeDifferentials_congr (Category.assoc ι' ι₀ sW), h]
      haveI hML : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨W.toRingedSpace.presheaf,
            W.toRingedSpace.IsSheaf⟩).obj
              (Scheme.Hom.relativeDifferentialForms sW ((d + 1 + 2 : ℕ) : ℤ))).obj
              ((Scheme.Modules.pullback ψ).obj (twistOne ℂ K))) :=
        Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible W.presheaf W.ringCatSheaf.2 _ _
      haveI hML' : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
          (Scheme.Hom.relativeDifferentialForms sW ((d + 1 + 2 : ℕ) : ℤ) ⊗
            (Scheme.Modules.pullback ψ).obj (twistOne ℂ K) : W.Modules) := hML
      haveI := MMP.Mori.isInvertible_pullback_obj ι₀
        (Scheme.Hom.relativeDifferentialForms sW ((d + 1 + 2 : ℕ) : ℤ) ⊗
            (Scheme.Modules.pullback ψ).obj (twistOne ℂ K) : W.Modules)
      haveI := MMP.Mori.isInvertible_pullback_obj ι₀ ((Scheme.Modules.pullback ψ).obj (twistOne ℂ K))
      have e₁ : Scheme.Hom.relativeDifferentialForms (ι₀ ≫ sW) ((d + 2 : ℕ) : ℤ) ≅
          (Scheme.Modules.pullback ι₀).obj
            (Scheme.Hom.relativeDifferentialForms sW ((d + 1 + 2 : ℕ) : ℤ) ⊗
              (Scheme.Modules.pullback ψ).obj (twistOne ℂ K)) :=
        eqToIso (by congr 1) ≪≫ eω ≪≫ eqToIso (by push_cast; rfl)
      have e₂ : (Scheme.Modules.pullback (ι₀ ≫ ψ)).obj (twistOne ℂ K) ≅
          (Scheme.Modules.pullback ι₀).obj ((Scheme.Modules.pullback ψ).obj (twistOne ℂ K)) :=
        ((Scheme.Modules.pullbackComp ι₀ ψ).app _).symm
      have ht : degreeOn ℂ sW (ι' ≫ ι₀) hC.le
          (Scheme.Hom.relativeDifferentialForms sW ((d + 1 + 2 : ℕ) : ℤ) ⊗
              (Scheme.Modules.pullback ψ).obj (twistOne ℂ K) : W.Modules) =
          degreeOn ℂ sW (ι' ≫ ι₀) hC.le
              (Scheme.Hom.relativeDifferentialForms sW ((d + 1 + 2 : ℕ) : ℤ)) +
            degreeOn ℂ sW (ι' ≫ ι₀) hC.le ((Scheme.Modules.pullback ψ).obj (twistOne ℂ K)) :=
        degreeOn_tensorSheaf ℂ sW (ι' ≫ ι₀) hC.le
          (Scheme.Hom.relativeDifferentialForms sW ((d + 1 + 2 : ℕ) : ℤ))
          ((Scheme.Modules.pullback ψ).obj (twistOne ℂ K))
      rw [degreeOn_eq_of_iso ℂ (ι₀ ≫ sW) ι' hC.le e₁, degreeOn_eq_of_iso ℂ (ι₀ ≫ sW) ι' hC.le e₂,
        degreeOn_pullback_eq_degreeOn_comp (ι₀ ≫ sW) sW ι₀ ι' rfl hC.le,
        degreeOn_pullback_eq_degreeOn_comp (ι₀ ≫ sW) sW ι₀ ι' rfl hC.le, ht]
      generalize degreeOn ℂ sW (ι' ≫ ι₀) hC.le
        (Scheme.Hom.relativeDifferentialForms sW ((d + 1 + 2 : ℕ) : ℤ)) = a
      generalize degreeOn ℂ sW (ι' ≫ ι₀) hC.le ((Scheme.Modules.pullback ψ).obj (twistOne ℂ K)) = b
      push_cast
      ring
    · obtain ⟨c', hc', hc'red⟩ := exists_isReduced_completeIntersection d
        ((hyperplaneSection χ x).subschemeι ≫ sY) ((hyperplaneSection χ x).subschemeι ≫ χ)
        (by rw [Category.assoc, hχ]) P' hP'
      refine ⟨Fin.cons x c', by rw [← hP'eq c']; exact hc', hred c' hc'red,
        fun hne => absurd ?_ hne₀⟩
      rw [hsup] at hne
      obtain ⟨w, hw⟩ := hne
      rw [Scheme.IdealSheafData.support_sup] at hw
      exact ⟨w, hw.1⟩

end Cut

section Embedding

open MMP.Threefold.Bridges MMP.Intersection Stacks.AmpleProjectiveImmersion

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The renaming isomorphism `ℙ^{ULift (Fin (M + 1))}_ℂ ≅ Proj ℂ[T₀, …, T_M]` lies over
`Spec ℂ`. -/
private theorem isoPolyGrading_hom_projModelToSpec (M : ℕ) :
    (ProjSpace.isoPolyGrading ℂ M).hom ≫ Stacks.ProjectiveCohomology.projModelToSpec ℂ M =
      ProjSpace.toSpec ℂ (ULift.{0} (Fin (M + 1))) := by
  rw [ProjSpace.isoPolyGrading_hom, Stacks.ProjectiveCohomology.projModelToSpec_eq,
    Proj.map_toSpecZero_assoc, ← Spec.map_comp, ProjSpace.toSpec,
    Stacks.ProjectiveCohomology.polyDegreeZeroHom, ← CommRingCat.ofHom_comp]
  congr 3
  refine RingHom.ext fun a => Subtype.ext ?_
  change MvPolynomial.rename ULift.up (MvPolynomial.C a) = MvPolynomial.C a
  exact MvPolynomial.rename_C _ _

/-- The base-change model of `ℙᴹ` over `Spec ℂ` and `Proj ℂ[T₀, …, T_M]`. -/
private noncomputable def projectiveSpaceOverIso (M : ℕ) :
    projectiveSpaceOver M (Spec (.of ℂ)) ≅ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ M) :=
  (ProjSpace.isoProjectiveSpaceOver ℂ M).symm ≪≫ ProjSpace.isoPolyGrading ℂ M

private theorem projectiveSpaceOverIso_hom_projModelToSpec (M : ℕ) :
    (projectiveSpaceOverIso M).hom ≫ Stacks.ProjectiveCohomology.projModelToSpec ℂ M =
      projectiveSpaceOver M (Spec (.of ℂ)) ↘ Spec (.of ℂ) := by
  rw [projectiveSpaceOverIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    isoPolyGrading_hom_projModelToSpec, Iso.inv_comp_eq, ProjSpace.isoProjectiveSpaceOver_hom_over]

/-- Under `projectiveSpaceOverIso`, `𝒪(1)` on `Proj ℂ[T₀, …, T_M]` pulls back to the hyperplane
sheaf of the base-change model. -/
private noncomputable def pullbackTwistOneIso (M : ℕ) :
    (Scheme.Modules.pullback (projectiveSpaceOverIso M).hom).obj (twistOne ℂ M) ≅
      projectiveSpaceTwistingSheaf M (Spec (.of ℂ)) :=
  ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback (ProjSpace.isoProjectiveSpaceOver ℂ M).inv).mapIso
      (ProjSpace.twistingSheafIsoPullback ℂ M 1 ≪≫ (ProjSpace.twistOneIsoPullback ℂ M).symm) ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (Iso.inv_hom_id _)).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _

/-- **Embeddings by the powers of an ample sheaf.** For an ample invertible `L` on a projective
`ℂ`-scheme `X`, every sufficiently large power `L^m` is `φ^* 𝒪(1)` for a closed embedding
`φ : X ⟶ ℙᴺ_ℂ` over `ℂ`. -/
private theorem exists_isClosedImmersion_twistOne_iso {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ (N : ℕ) (φ : X ⟶ AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N)),
      IsClosedImmersion φ ∧ φ ≫ Stacks.ProjectiveCohomology.projModelToSpec ℂ N = sX ∧
      Nonempty (Stacks.Ample.tensorPowModule X L (m : ℤ) ≅
        (Scheme.Modules.pullback φ).obj (twistOne ℂ N)) := by
  obtain ⟨m₀, hm₀, h⟩ :=
    MMP.Resolution.eventually_isRelativelyVeryAmple_and_isClosedImmersion_of_isAmple sX hX L hL
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨-, M, i, hi, hover, ⟨e⟩⟩ := h m hm
  haveI := hi
  refine ⟨M, i ≫ (projectiveSpaceOverIso M).hom, inferInstance, ?_, ⟨e ≪≫ ?_⟩⟩
  · rw [Category.assoc, projectiveSpaceOverIso_hom_projModelToSpec, hover]
  · exact (Scheme.Modules.pullback i).mapIso (pullbackTwistOneIso M).symm ≪≫
      (Scheme.Modules.pullbackComp _ _).app _

/-- A projective `ℂ`-scheme carries an ample invertible sheaf. -/
private theorem exists_isAmple_of_isProjectiveMorphism {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjectiveMorphism sX) :
    ∃ (L : X.Modules) (_ : Stacks.Ample.IsInvertibleModule X L), Stacks.Ample.IsAmple X L := by
  obtain ⟨M, i, hi, -⟩ := hX
  haveI := hi
  have h := Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf M (Spec (.of ℂ))
  have h' := Scheme.Modules.isAmple_pullback_of_isClosedImmersion i _
    ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr h)
  exact ⟨_, Stacks.InvertiblePullback.isInvertibleModule_pullback i _,
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp h'⟩

end Embedding

section Generation

open MonoidalCategory

/-- **A lower bound for degrees from ample twists.** For an ample invertible `L` and an invertible
`F` on a scheme `U` over `ℂ`, there is `n` such that `deg_C F ≥ -n · deg_C L` for every proper
integral curve `j : C ⟶ U`: `F ⊗ L^n` is globally generated, so it has nonnegative degree on
`C`. -/
private theorem exists_neg_mul_degreeOn_le_of_isAmple {U : Scheme.{0}} (sU : U ⟶ Spec (.of ℂ))
    (L F : U.Modules) [Stacks.Ample.IsInvertibleModule U L] [Stacks.Ample.IsInvertibleModule U F]
    (hL : Stacks.Ample.IsAmple U L) :
    ∃ n : ℕ, ∀ {C : Scheme.{0}} (j : C ⟶ U) [IsProper (j ≫ sU)] [IsIntegral C]
      (hC : topologicalKrullDim C ≤ 1),
      -((n : ℤ) * degreeOn ℂ sU j hC L) ≤ degreeOn ℂ sU j hC F := by
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple L hL
    (Stacks.Ample.tensorPowModule U F 1)
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule F 1)
    (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _)
  refine ⟨n₀.toNat, fun {C} j _ _ hC => ?_⟩
  obtain ⟨σ, -⟩ := hn₀ (n₀.toNat : ℤ) (Int.self_le_toNat n₀)
  -- the generators, read in the sheaf tensor product
  let G : U.Modules := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨U.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ U.presheaf (forget₂ CommRingCat RingCat)
      U.ringCatSheaf.2⟩).obj (Stacks.Ample.tensorPowModule U F 1)).obj
      (Stacks.Ample.tensorPowModule U L (n₀.toNat : ℤ))
  let e := Stacks.SheafOfModules.tensorObjIso U.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf U)
    (Stacks.Ample.tensorPowModule U F 1) (Stacks.Ample.tensorPowModule U L (n₀.toNat : ℤ))
  let τ : G.GeneratingSections := SheafOfModules.GeneratingSections.equivOfIso e σ
  haveI : SheafOfModules.IsInvertible U.presheaf U.ringCatSheaf.2 G :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible U.presheaf U.ringCatSheaf.2 _ _
  haveI := MMP.Mori.isInvertible_pullback_obj j G
  -- the pulled-back generators
  let σ' : ((Scheme.Modules.pullback j).obj G).GeneratingSections := by
    change ((RingedSpaceModuleAdjunction.modulePullback j.toLRSHom.toShHom).obj
      G).GeneratingSections
    exact Stacks.SheafOfModules.modulePullbackGeneratingSections j.toLRSHom.toShHom G τ
  have h0 : 0 ≤ degreeOn ℂ sU j hC G := by
    obtain ⟨c⟩ : Nonempty C := inferInstance
    haveI := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _
      ((Scheme.Modules.pullback j).obj G)
    obtain ⟨i, hi⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing _ σ' c
    exact invertibleCurveDegree_nonneg_of_eval_top_ne_zero ℂ (j ≫ sU) hC _ (σ'.s i)
      (eval_top_ne_zero_of_mem_nonvanishingLocus _ _ hi)
  have ht : degreeOn ℂ sU j hC G = degreeOn ℂ sU j hC (Stacks.Ample.tensorPowModule U F 1) +
      degreeOn ℂ sU j hC (Stacks.Ample.tensorPowModule U L (n₀.toNat : ℤ)) :=
    degreeOn_tensorSheaf ℂ sU j hC (Stacks.Ample.tensorPowModule U F 1)
      (Stacks.Ample.tensorPowModule U L (n₀.toNat : ℤ))
  have hF : degreeOn ℂ sU j hC (Stacks.Ample.tensorPowModule U F 1) = degreeOn ℂ sU j hC F :=
    degreeOn_eq_of_iso ℂ sU j hC (Stacks.Ample.tensorPowModuleOneIso U F)
  have hLn : degreeOn ℂ sU j hC (Stacks.Ample.tensorPowModule U L (n₀.toNat : ℤ)) =
      (n₀.toNat : ℤ) * degreeOn ℂ sU j hC L := by
    haveI : Stacks.Ample.IsInvertibleModule C ((Scheme.Modules.pullback j).obj L) :=
      Stacks.InvertiblePullback.isInvertibleModule_pullback j L
    rw [degreeOn_eq_invertibleCurveDegree, degreeOn_eq_invertibleCurveDegree,
      ← MMP.Fourfold.invertibleCurveDegree_tensorPowModule_natCast (j ≫ sU) hC _ n₀.toNat]
    exact invertibleCurveDegree_eq_of_iso ℂ (j ≫ sU) hC
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso j L n₀.toNat)
  rw [ht, hF, hLn] at h0
  linarith

end Generation

section Normalization

open Scheme.IdealSheafData

/-- **Cutting a morphism which is an isomorphism over an open.** If `ν : V ⟶ E` is an isomorphism
over `O`, then for a closed subscheme `C = V(A)` of `E` the restriction `V(ν^* A) ⟶ C` of `ν` is
an isomorphism over `C ∩ O`: the square of closed immersions is cartesian, and so is its
restriction over `O`. -/
private theorem isIso_subschemeMap_comap_morphismRestrict {E V : Scheme.{0}} (ν : V ⟶ E)
    (O : E.Opens) [IsIso (ν ∣_ O)] (A : E.IdealSheafData) :
    IsIso (subschemeMap (A.comap ν) A ν (A.le_map_comap ν) ∣_ (A.subschemeι ⁻¹ᵁ O)) := by
  set π := subschemeMap (A.comap ν) A ν (A.le_map_comap ν) with hπdef
  set W := A.subschemeι ⁻¹ᵁ O with hW
  have hπ : π ≫ A.subschemeι = (A.comap ν).subschemeι ≫ ν := subschemeMap_subschemeι _ _ _ _
  have sq : IsPullback (A.comap ν).subschemeι π ν A.subschemeι :=
    isPullback_of_isClosedImmersion _ _ π ν hπ.symm (by rw [ker_subschemeι, ker_subschemeι])
  have big := (isPullback_morphismRestrict π W).paste_vert sq.flip
  have hrange : Set.range ((π ⁻¹ᵁ W).ι ≫ (A.comap ν).subschemeι) ⊆ Set.range (ν ⁻¹ᵁ O).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ν ((A.comap ν).subschemeι ((π ⁻¹ᵁ W).ι z)) ∈ O
    rw [← Scheme.Hom.comp_apply, ← hπ, Scheme.Hom.comp_apply]
    exact z.2
  set t := IsOpenImmersion.lift (ν ⁻¹ᵁ O).ι _ hrange with ht
  have hsq : IsPullback (π ∣_ W) t (A.subschemeι ∣_ O) (ν ∣_ O) := by
    refine IsPullback.of_bot (h₃₁ := ν) ?_ ?_ (isPullback_morphismRestrict ν O)
    · rw [ht, IsOpenImmersion.lift_fac, morphismRestrict_ι]
      exact big
    · rw [← cancel_mono O.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
        morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι, ht,
        IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, ← hπ]
  exact hsq.isIso_fst_of_isIso

/-- **The degree on a curve and on its preimage under a map which is an isomorphism over an open
meeting the curve.** Let `ν : V ⟶ E` be finite and an isomorphism over `O`, and `C = V(A)` an
integral proper curve in `E` meeting `O` whose preimage `Cᵛ = V(ν^* A)` is an integral curve.
Then `Cᵛ ⟶ C` is a finite birational morphism of integral curves, so an invertible `M` on `E`
has the same degree on `C` and on `Cᵛ`. -/
private theorem degreeOn_comp_comap_eq_of_isIso_morphismRestrict {E V : Scheme.{0}}
    (sE : E ⟶ Spec (.of ℂ)) [IsSeparated sE] [LocallyOfFiniteType sE] (ν : V ⟶ E) [IsFinite ν]
    (O : E.Opens) [IsIso (ν ∣_ O)] (A : E.IdealSheafData) [IsIntegral A.subscheme]
    [IsIntegral (A.comap ν).subscheme] (hA : topologicalKrullDim A.subscheme = 1)
    (hAν : topologicalKrullDim (A.comap ν).subscheme = 1)
    (hW : ((A.subschemeι ⁻¹ᵁ O : A.subscheme.Opens) : Set A.subscheme).Nonempty)
    [IsProper (A.subschemeι ≫ sE)] [IsProper (((A.comap ν).subschemeι ≫ ν) ≫ sE)]
    (M : E.Modules) [SheafOfModules.IsInvertible E.presheaf E.ringCatSheaf.2 M] :
    degreeOn ℂ sE ((A.comap ν).subschemeι ≫ ν) hAν.le M = degreeOn ℂ sE A.subschemeι hA.le M := by
  set π := subschemeMap (A.comap ν) A ν (A.le_map_comap ν) with hπdef
  set W := A.subschemeι ⁻¹ᵁ O with hWdef
  have hπ : π ≫ A.subschemeι = (A.comap ν).subschemeι ≫ ν := subschemeMap_subschemeι _ _ _ _
  haveI : IsIso (π ∣_ W) := isIso_subschemeMap_comap_morphismRestrict ν O A
  -- `π` is birational
  obtain ⟨w, hw⟩ := hW
  have hU : ((π ⁻¹ᵁ W : (A.comap ν).subscheme.Opens) : Set (A.comap ν).subscheme).Nonempty := by
    refine ⟨((π ⁻¹ᵁ W).ι) (inv (π ∣_ W) ⟨w, hw⟩), ?_⟩
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  have hbir : MMP.Mori.IsBirationalMorphism π :=
    MMP.Flips.isBirationalMorphism_of_isIso_resLE π (π ⁻¹ᵁ W) W hU ⟨w, hw⟩ le_rfl
      (by rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance)
  -- the two curves
  haveI : AlgebraicGeometry.IsVariety ℂ (A.subschemeι ≫ sE) := { toIsIntegral := inferInstance }
  haveI : AlgebraicGeometry.IsCurve ℂ (A.subschemeι ≫ sE) := { topologicalKrullDim_eq_one := hA }
  haveI : AlgebraicGeometry.IsVariety ℂ (((A.comap ν).subschemeι ≫ ν) ≫ sE) :=
    { toIsIntegral := inferInstance }
  haveI : AlgebraicGeometry.IsCurve ℂ (((A.comap ν).subschemeι ≫ ν) ≫ sE) :=
    { topologicalKrullDim_eq_one := hAν }
  have hh : π ≫ A.subschemeι ≫ sE = ((A.comap ν).subschemeι ≫ ν) ≫ sE := by
    rw [← Category.assoc, hπ]
  -- `π` is not constant: it is an isomorphism over the nonempty open `W` of a curve
  have hnc : ¬ ∃ y : A.subscheme, ∀ x : (A.comap ν).subscheme, π.base x = y := by
    rintro ⟨y, hy⟩
    have hinj := (Scheme.homeoOfIso (asIso (π ∣_ W))).injective
    have hwy : w = y := by
      obtain ⟨z, hz⟩ := (Scheme.homeoOfIso (asIso (π ∣_ W))).surjective ⟨w, hw⟩
      have hz' := congrArg Subtype.val hz
      change ((π ∣_ W) z).1 = w at hz'
      rw [morphismRestrict_base_coe] at hz'
      exact hz'.symm.trans (hy _)
    have hmem : ∀ x : (A.comap ν).subscheme, x ∈ π ⁻¹ᵁ W := fun x => by
      change π x ∈ W
      rw [hy, ← hwy]
      exact hw
    haveI hsub : Subsingleton (A.comap ν).subscheme := by
      refine ⟨fun x₁ x₂ => ?_⟩
      have h : (π ∣_ W) ⟨x₁, hmem x₁⟩ = (π ∣_ W) ⟨x₂, hmem x₂⟩ :=
        Subtype.ext <| (morphismRestrict_base_coe π W ⟨x₁, hmem x₁⟩).trans
          (((hy x₁).trans (hy x₂).symm).trans (morphismRestrict_base_coe π W ⟨x₂, hmem x₂⟩).symm)
      exact congrArg Subtype.val (hinj h)
    haveI : DiscreteTopology (A.comap ν).subscheme := Subsingleton.discreteTopology
    have h0 := topologicalKrullDim_zero_of_discreteTopology (A.comap ν).subscheme
    rw [hAν] at h0
    exact absurd h0 (by decide)
  haveI := MMP.Mori.isInvertible_pullback_obj A.subschemeι M
  have key := invertibleCurveDegree_pullback_eq_degreeOver_mul ℂ
    (((A.comap ν).subschemeι ≫ ν) ≫ sE) (A.subschemeι ≫ sE) π hh hnc
    ((Scheme.Modules.pullback A.subschemeι).obj M)
  haveI := locallyOfFiniteType_of_isCurve_comp ℂ (((A.comap ν).subschemeι ≫ ν) ≫ sE)
    (A.subschemeι ≫ sE) π hh
  haveI := isDominant_of_not_constant ℂ (((A.comap ν).subschemeι ≫ ν) ≫ sE)
    (A.subschemeι ≫ sE) π hnc
  
  have hdeg : @degreeOver _ _ π _ _ (locallyOfFiniteType_of_isCurve_comp ℂ
      (((A.comap ν).subschemeι ≫ ν) ≫ sE) (A.subschemeι ≫ sE) π hh)
      (isDominant_of_not_constant ℂ (((A.comap ν).subschemeι ≫ ν) ≫ sE)
        (A.subschemeι ≫ sE) π hnc) = 1 := by
    letI := (functionFieldMap π).toAlgebra
    have heq : functionFieldMap π = dominantFunctionFieldMap π :=
      (congrArg CommRingCat.Hom.hom
        (stalkMap_cast_target π (genericPoint _) (map_genericPoint_of_isDominant π))).symm
    rw [degreeOver_eq_finrank π heq]
    let e := AlgEquiv.ofBijective (Algebra.ofId A.subscheme.functionField
      (A.comap ν).subscheme.functionField) hbir.functionFieldMap_bijective
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  rw [hdeg, Nat.cast_one, one_mul] at key
  rw [degreeOn_eq_invertibleCurveDegree, degreeOn_eq_invertibleCurveDegree, ← key]
  haveI := MMP.Mori.isInvertible_pullback_obj π ((Scheme.Modules.pullback A.subschemeι).obj M)
  exact invertibleCurveDegree_eq_of_iso ℂ _ _
    ((Scheme.Modules.pullbackCongr hπ.symm).app M ≪≫ ((Scheme.Modules.pullbackComp _ _).app M).symm)

end Normalization

section AssemblyHelpers

/-- The degree of an invertible module depends only on the structure morphism, not on how it is
written. -/
private theorem invertibleCurveDegree_congr_hom {C : Scheme.{0}} {f g : C ⟶ Spec (.of ℂ)}
    (h : f = g) [IsProper f] [IsProper g] {hC : topologicalKrullDim C ≤ 1} (L : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L] :
    invertibleCurveDegree ℂ f hC L = invertibleCurveDegree ℂ g hC L := by
  subst h
  rfl

/-- **A closed subscheme of an open, as a closed subscheme of the whole.** If the closed subscheme
`V(I)` of `V` lies in the open `U`, a closed immersion into `U` with ideal `I|_U` is, over `V`,
the closed subscheme `V(I)`. -/
private theorem exists_iso_subscheme_of_ker_eq_comap {V C : Scheme.{0}} (U : V.Opens)
    (I : V.IdealSheafData) (hI : Set.range I.subschemeι ⊆ U) (ι : C ⟶ U.toScheme)
    [IsClosedImmersion ι] (hker : ι.ker = I.comap U.ι) :
    ∃ e : C ≅ I.subscheme, e.hom ≫ I.subschemeι = ι ≫ U.ι := by
  -- `C ≅ V(I|_U)` over `U`
  let a := IsClosedImmersion.lift (I.comap U.ι).subschemeι ι
    (by rw [Scheme.IdealSheafData.ker_subschemeι, hker])
  have ha : a ≫ (I.comap U.ι).subschemeι = ι := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso a := IsClosedImmersion.isIso_of_ker_eq ι (I.comap U.ι).subschemeι a ha
    (by rw [Scheme.IdealSheafData.ker_subschemeι, hker])
  -- `V(I|_U) ≅ V(I)` over `V`, the latter lying in `U`
  haveI : IsOpenImmersion (Limits.pullback.snd U.ι I.subschemeι) := inferInstance
  haveI : Surjective (Limits.pullback.snd U.ι I.subschemeι) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨u, hu⟩ : I.subschemeι x ∈ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]; exact hI ⟨x, rfl⟩
    obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback u x hu
    exact ⟨p, hp⟩
  haveI : IsIso (Limits.pullback.snd U.ι I.subschemeι) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  refine ⟨asIso a ≪≫ I.comapIso U.ι ≪≫ asIso (Limits.pullback.snd U.ι I.subschemeι), ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← Limits.pullback.condition, ← Category.assoc (I.comapIso U.ι).hom,
    Scheme.IdealSheafData.comapIso_hom_fst, ← Category.assoc, ha]

/-- `deg_C(L^{⊗ m}) = m · deg_C L`. -/
private theorem degreeOn_tensorPowModule_natCast' {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (z : Z ⟶ X) [IsProper (z ≫ sX)] (hdim : topologicalKrullDim Z ≤ 1) (H : X.Modules)
    [Stacks.Ample.IsInvertibleModule X H] (m : ℕ) :
    degreeOn ℂ sX z hdim (Stacks.Ample.tensorPowModule X H (m : ℤ)) =
      m * degreeOn ℂ sX z hdim H := by
  haveI : Stacks.Ample.IsInvertibleModule Z ((Scheme.Modules.pullback z).obj H) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback z H
  rw [degreeOn_eq_invertibleCurveDegree, degreeOn_eq_invertibleCurveDegree,
    ← MMP.Fourfold.invertibleCurveDegree_tensorPowModule_natCast (z ≫ sX) hdim _ m]
  exact invertibleCurveDegree_eq_of_iso ℂ (z ≫ sX) hdim
    (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso z H m)

/-- `a + 1 ≤ m + 1` in `WithBot ℕ∞` gives `a ≤ m`. -/
private theorem withBot_le_of_add_one_le {a : WithBot ℕ∞} {m : ℕ}
    (h : a + 1 ≤ ((m + 1 : ℕ) : WithBot ℕ∞)) : a ≤ (m : WithBot ℕ∞) := by
  cases a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    cases e using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [h1] at h
      have := WithBot.coe_le_coe.mp h
      exact absurd this (by simp)
    | coe k =>
      have h' : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((m + 1 : ℕ) : WithBot ℕ∞) := by
        push_cast; exact h
      have : k + 1 ≤ m + 1 := by exact_mod_cast h'
      exact_mod_cast (by omega : k ≤ m)

/-- `a + m ≤ m` in `WithBot ℕ∞` gives `a ≤ 0`. -/
private theorem withBot_le_zero_of_add_le {a : WithBot ℕ∞} {m : ℕ}
    (h : a + (m : WithBot ℕ∞) ≤ (m : WithBot ℕ∞)) : a ≤ 0 := by
  cases a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    cases e using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + (m : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [show (m : WithBot ℕ∞) = ((m : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_add, top_add]
      rw [h1] at h
      have := WithBot.coe_le_coe.mp h
      exact absurd this (by simp)
    | coe k =>
      have h' : ((k + m : ℕ) : WithBot ℕ∞) ≤ ((m : ℕ) : WithBot ℕ∞) := by
        push_cast; exact h
      have : k + m ≤ m := by exact_mod_cast h'
      exact_mod_cast (by omega : k ≤ 0)

/-- A space whose Krull dimension is a natural number is nonempty. -/
private theorem nonempty_of_topologicalKrullDim_eq {X : Type*} [TopologicalSpace X] {m : ℕ}
    (h : topologicalKrullDim X = (m : WithBot ℕ∞)) : Nonempty X := by
  by_contra hX
  rw [not_nonempty_iff] at hX
  have h0 : topologicalKrullDim X = ⊥ := by
    rw [topologicalKrullDim, Order.krullDim_eq_bot_iff]
    exact ⟨fun T => hX.elim T.isIrreducible.nonempty.some⟩
  rw [h] at h0
  exact WithBot.coe_ne_bot h0

/-- An injective morphism from a scheme of dimension one has a range that is not a
subsingleton. -/
private theorem not_subsingleton_range_of_topologicalKrullDim_eq_one {C Y : Scheme.{0}}
    (f : C ⟶ Y) (hf : Function.Injective f.base) (hC : topologicalKrullDim C = 1) :
    ¬ (Set.range f.base).Subsingleton := by
  intro hs
  haveI : Subsingleton C := ⟨fun a b => hf (hs ⟨a, rfl⟩ ⟨b, rfl⟩)⟩
  haveI : DiscreteTopology C := Subsingleton.discreteTopology
  have h0 := topologicalKrullDim_zero_of_discreteTopology C
  rw [hC] at h0
  exact absurd h0 (by decide)

end AssemblyHelpers

section SmoothLocus

/-- An open subscheme of the smooth locus of a variety of dimension `r` is smooth of relative
dimension `r`. -/
private theorem smoothOfRelativeDimension_of_le_smoothLocus {k : Type} [Field k]
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sV] {r : ℕ}
    (hr : topologicalKrullDim V = r) (U : V.Opens) (hU : U ≤ smoothLocus sV) :
    SmoothOfRelativeDimension r (U.ι ≫ sV) := by
  by_cases hne : Nonempty U
  · haveI : Smooth (U.ι ≫ sV) := by
      rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
        ← smoothLocus_eq_smoothLocus, eq_top_iff]
      intro x _
      exact hU x.2
    haveI : AlgebraicGeometry.IsVariety k (U.ι ≫ sV) :=
      Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sV U
    have hdim : topologicalKrullDim U = r :=
      (Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens k sV U).trans hr
    exact MMP.Intersection.smoothOfRelativeDimension_of_isVariety _ r hdim
  · haveI : IsEmpty U := not_nonempty_iff.mp hne
    exact ⟨isEmptyElim⟩

end SmoothLocus

section Image

variable {k : Type} [Field k] [IsAlgClosed k]

/-- **The image of a rational curve.** Let `g : V ⟶ X` be a `k`-morphism to a proper variety and
`L ⊆ V` a rational curve on which the pull-back of an invertible sheaf `M` on `X` has positive
degree. Then `g(L)` is a rational proper curve `T ⊆ X` and `deg_L g^*M = e · deg_T M` for the
degree `e ≥ 1` of `L ⟶ T`. -/
private theorem exists_properCurve_image_of_isRationalCurve {V X : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsProperVariety k sX]
    (g : V ⟶ X)
    (hg : g ≫ sX = sV) (L : V.IdealSheafData) (hL : IsRationalCurve sV L) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (hpos : haveI := hL.2.1
      0 < degreeOn k sV L.subschemeι hL.1.2.le ((Scheme.Modules.pullback g).obj M)) :
    ∃ T : ProperCurve sX,
      IsRationalCurve sX
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) ∧
        closure ({T.point} : Set X) ⊆ Set.range g ∧
        ∃ e : ℕ, 0 < e ∧ (haveI := hL.2.1
          degreeOn k sV L.subschemeι hL.1.2.le ((Scheme.Modules.pullback g).obj M) =
            e * degreeOn k sX T.ι T.dim_le M) := by
  haveI := hL.2.1
  haveI : IsIntegral L.subscheme := hL.1.1
  set φ := L.subschemeι ≫ g with hφdef
  have hφs : φ ≫ sX = L.subschemeι ≫ sV := by rw [hφdef, Category.assoc, hg]
  haveI : IsProper (φ ≫ sX) := hφs ▸ inferInstance
  haveI : AlgebraicGeometry.IsCurve k (L.subschemeι ≫ sV) :=
    { toIsIntegral := inferInstance
      toIsSeparated := hL.2.1.toIsSeparated
      toLocallyOfFiniteType := hL.2.1.toLocallyOfFiniteType
      toQuasiCompact := by haveI := hL.2.1; infer_instance
      topologicalKrullDim_eq_one := hL.1.2 }
  haveI : AlgebraicGeometry.IsCurve k (φ ≫ sX) := hφs ▸ inferInstance
  have hdeg := degreeOn_pullback_eq_degreeOn_comp sV sX g L.subschemeι hg hL.1.2.le M
  have hnc : ¬ ∃ y : X, Set.range φ = {y} := by
    intro hpt
    have h0 := degreeOn_eq_zero_of_range_eq_singleton sX φ M hpt
    rw [hdeg] at hpos
    exact absurd h0 hpos.ne'
  haveI : IsProper φ := IsProper.of_comp φ sX
  set y₀ := φ (genericPoint L.subscheme) with hy₀
  have hrange : closure (Set.range φ) = closure ({y₀} : Set X) := by
    refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
    · rintro _ ⟨c, rfl⟩
      have hc : c ∈ closure ({genericPoint L.subscheme} : Set L.subscheme) := by
        rw [(genericPoint_spec L.subscheme).def]; trivial
      have := image_closure_subset_closure_image φ.continuous (Set.mem_image_of_mem φ hc)
      rwa [Set.image_singleton] at this
    · rintro _ rfl; exact ⟨_, rfl⟩
  have hclosed : IsClosed (Set.range φ) := φ.isClosedMap.isClosed_range
  have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {y₀}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    exact Closeds.ext (by rw [Closeds.coe_closure, Closeds.coe_closure, hrange])
  have hcurve := isCurve_imageι_comp sX φ hnc
  have hdim : topologicalKrullDim (curveSubschemeAt y₀) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι y₀ ≫ sX) := by
    have h1 : IsProper (φ.imageι ≫ sX) := isProper_imageι_comp φ sX
    change IsProper (φ.ker.subschemeι ≫ sX) at h1
    rwa [hker] at h1
  let T : ProperCurve sX := ⟨y₀, ⟨hdim, hprop⟩⟩
  have hnc' : ¬ (g.base '' (L.support : Set V)).Subsingleton := by
    intro hsub
    apply hnc
    obtain ⟨c⟩ : Nonempty L.subscheme := inferInstance
    refine ⟨φ c, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨c, rfl⟩, ?_⟩⟩
    rintro _ ⟨d, rfl⟩
    have hmem : ∀ e : L.subscheme, φ e ∈ g.base '' (L.support : Set V) := fun e =>
      ⟨L.subschemeι e, by rw [← L.range_subschemeι]; exact ⟨e, rfl⟩, rfl⟩
    exact hsub (hmem d) (hmem c)
  have hrat := IsRationalCurve.ker_subschemeι_comp hg hL hnc'
  haveI : UniversallyClosed φ := ‹IsProper φ›.toUniversallyClosed
  haveI : LocallyOfFiniteType φ := ‹IsProper φ›.toLocallyOfFiniteType
  haveI : QuasiCompact φ := ⟨fun _ _ => φ.isProperMap.isCompact_preimage⟩
  haveI : IsIntegral φ.image := MMP.Mori.isIntegral_image φ
  haveI : LocallyOfFiniteType φ.toImage := MMP.Mori.locallyOfFiniteType_toImage φ
  refine ⟨T, ?_, ?_, degreeOver φ.toImage, ?_, ?_⟩
  · rw [← hker]; exact hrat
  · change closure ({y₀} : Set X) ⊆ Set.range g
    rw [← hrange, hclosed.closure_eq]
    rintro _ ⟨c, rfl⟩
    exact ⟨_, rfl⟩
  · have hmul := degreeOn_eq_degreeOver_mul sX φ M hnc
    by_contra h0
    have he : degreeOver φ.toImage = 0 := by omega
    rw [hdeg, hmul, he] at hpos
    simp at hpos
  · haveI : IsProper (φ.ker.subschemeι ≫ sX) := isProper_imageι_comp φ sX
    have hcongr : degreeOn k sX φ.imageι (topologicalKrullDim_image_le_one sX φ) M =
        degreeOn k sX T.ι T.dim_le M :=
      degreeOn_subschemeι_congr hker _ _ M
    rw [hdeg, degreeOn_eq_degreeOver_mul sX φ M hnc, hcongr]

end Image

section Component

open Topology

/-- **A component of maximal dimension.** A nonempty closed subset `F` of a Noetherian
quasi-sober space contains the closure of a point whose dimension is that of `F`. -/
private theorem exists_closure_singleton_subset_topologicalKrullDim_eq {T : Type*}
    [TopologicalSpace T] [QuasiSober T] [NoetherianSpace T] {F : Set T} (hF : IsClosed F)
    (hne : F.Nonempty) :
    ∃ η : T, closure ({η} : Set T) ⊆ F ∧
      topologicalKrullDim (closure ({η} : Set T)) = topologicalKrullDim F := by
  haveI : Nonempty F := hne.to_subtype
  obtain ⟨x⟩ := ‹Nonempty F›
  obtain ⟨W₀, hW₀, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({x} : Set F) isIrreducible_singleton
  obtain ⟨W, hW, hmax⟩ := Set.exists_max_image (irreducibleComponents F)
    (fun W : Set F => topologicalKrullDim W) NoetherianSpace.finite_irreducibleComponents
    ⟨W₀, hW₀⟩
  have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
  set W' : Set T := Subtype.val '' W with hW'
  have hW'i : IsIrreducible W' := hW.1.image _ continuous_subtype_val.continuousOn
  have hW'c : IsClosed W' := hF.isClosedEmbedding_subtypeVal.isClosedMap _ hWc
  obtain ⟨η, hη⟩ := QuasiSober.sober hW'i hW'c
  have hcl : closure ({η} : Set T) = W' := hη
  have hdimW : topologicalKrullDim W = topologicalKrullDim F := by
    refine le_antisymm (topologicalKrullDim_subspace_le _ _) ?_
    rw [AlgebraicGeometry.topologicalKrullDim_eq_iSup_irreducibleComponents F]
    exact iSup₂_le fun V hV => hmax V hV
  refine ⟨η, hcl ▸ Set.image_subset_iff.mpr fun w _ => w.2, ?_⟩
  rw [← hdimW, hcl]
  refine le_antisymm ?_ ?_
  · have hsub : W' ⊆ F := Set.image_subset_iff.mpr fun w _ => w.2
    have hmem : ∀ w : W', (⟨w.1, hsub w.2⟩ : F) ∈ W := by
      rintro ⟨_, y, hyW, rfl⟩; exact hyW
    let g : W' → W := fun w => ⟨⟨w.1, hsub w.2⟩, hmem w⟩
    refine IsInducing.topologicalKrullDim_le (f := g) ?_
    refine IsInducing.of_comp (g := Subtype.val ∘ Subtype.val) (by fun_prop) (by fun_prop) ?_
    exact IsInducing.subtypeVal
  · let g : W → W' := fun w => ⟨w.1.1, w.1, w.2, rfl⟩
    refine IsInducing.topologicalKrullDim_le (f := g) ?_
    refine IsInducing.of_comp (g := Subtype.val) (by fun_prop) (by fun_prop) ?_
    have : IsInducing ((Subtype.val : F → T) ∘ (Subtype.val : W → F)) :=
      IsInducing.subtypeVal.comp IsInducing.subtypeVal
    exact this

end Component

section Codimension

/-- The dimension of the image of a subset under a topological embedding is its dimension. -/
private theorem topologicalKrullDim_image_of_isEmbedding' {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] {f : S → T} (hf : Topology.IsEmbedding f) (A : Set S) :
    topologicalKrullDim (f '' A) = topologicalKrullDim A := by
  have hemb : Topology.IsEmbedding (fun x : A => f x.1) := hf.comp Topology.IsEmbedding.subtypeVal
  rw [Set.image_eq_range, ← IsHomeomorph.topologicalKrullDim_eq _ hemb.toHomeomorph.isHomeomorph]

/-- **Closed sets of large codimension.** On an integral scheme of finite type over a field, of
dimension `n + r`, a closed set all of whose points have coheight at least `r` has dimension at
most `n`: `dim {y}⁻ + coheight y = n + r` for every point `y`. -/
private theorem topologicalKrullDim_le_of_le_coheight {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {n r : ℕ}
    (hY : topologicalKrullDim Y = ((n + r : ℕ) : WithBot ℕ∞)) {S : Set Y} (hS : IsClosed S)
    (h : ∀ y ∈ S, (r : ℕ∞) ≤ Order.coheight y) : topologicalKrullDim S ≤ (n : WithBot ℕ∞) := by
  refine topologicalKrullDim_le_of_forall_closure hS fun y hy => ?_
  have hsum := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY y
  rw [hY] at hsum
  have hr := h y hy
  generalize topologicalKrullDim (closure ({y} : Set Y)) = a at hsum ⊢
  generalize Order.coheight y = c at hsum hr
  cases a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    cases a using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + (c : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, top_add]
      rw [h1] at hsum
      exact ENat.top_ne_coe _ (WithBot.coe_eq_coe.mp hsum)
    | coe a =>
      cases c using ENat.recTopCoe with
      | top =>
        exfalso
        have h1 : (((a : ℕ∞) : WithBot ℕ∞) + (((⊤ : ℕ∞) : ℕ∞) : WithBot ℕ∞)) =
            ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_add, add_top]
        rw [h1] at hsum
        exact ENat.top_ne_coe _ (WithBot.coe_eq_coe.mp hsum)
      | coe c =>
        have h1 : ((a + c : ℕ) : WithBot ℕ∞) = ((n + r : ℕ) : WithBot ℕ∞) := by
          rw [← hsum]; push_cast; rfl
        have h2 : a + c = n + r := by exact_mod_cast h1
        have h3 : r ≤ c := by exact_mod_cast hr
        exact_mod_cast (by omega : a ≤ n)

/-- **A normal variety is smooth in codimension one.** Over a perfect field, every point of a
normal variety off its smooth locus has coheight at least two: the generic point and the generic
points of prime divisors are smooth points. -/
private theorem two_le_coheight_of_notMem_smoothLocus {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {y : X}
    (hy : y ∉ smoothLocus sX) : (2 : ℕ∞) ≤ Order.coheight y := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  by_contra h
  push Not at h
  have h' : Order.coheight y = 0 ∨ Order.coheight y = 1 := by
    generalize Order.coheight y = a at h ⊢
    cases a using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe a =>
      have : a < 2 := by exact_mod_cast h
      interval_cases a <;> simp
  rcases h' with h0 | h1
  · apply hy
    have hle : y ≤ genericPoint X := (genericPoint_spec X).specializes (Set.mem_univ y)
    have : y = genericPoint X := (Specializes.antisymm (Order.coheight_eq_zero.1 h0 hle) hle).eq
    rw [this]
    exact MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus' (f := sX)
  · apply hy
    have := MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hX
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y h1)
    change AlgebraicGeometry.PrimeDivisor.genericPoint _ ∈ _ at this
    rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] at this

/-- The points of the support of a divisor have coheight at least one. -/
private theorem one_le_coheight_of_mem_supp {X : Scheme.{0}} {D : Divisor X} {y : X}
    (hy : y ∈ D.supp) : (1 : ℕ∞) ≤ Order.coheight y := by
  obtain ⟨E, -, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hy
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
  have hle : y ≤ E.genericPoint := specializes_iff_mem_closure.2 hyE
  have h1 := Order.coheight_anti hle
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E] at h1
  exact h1

end Codimension

section Main

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sX] [CompactSpace X]

set_option backward.isDefEq.respectTransparency false in
/-- A contraction which is not an isomorphism has a positive-dimensional fibre over a closed
point. -/
private theorem exists_isClosed_topologicalKrullDim_fibre_pos {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : IsContraction sX sZ f) (hnt : ¬ IsIso f) :
    ∃ z : Z, IsClosed ({z} : Set Z) ∧ 0 < topologicalKrullDim (f ⁻¹' {z}) := by
  by_contra! H
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  haveI := hf.isNormalVariety_target.1
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  let ι := {V : Z.Opens // IsFinite (f ∣_ V)}
  have hcov : ⨆ V : ι, V.1 = ⊤ := by
    by_contra hne
    obtain ⟨z, hz, hzc⟩ := IsClosed.exists_closed_singleton
      (S := ((⨆ V : ι, V.1 : Z.Opens) : Set Z)ᶜ) (Opens.isOpen _).isClosed_compl
      (by
        rw [Set.nonempty_compl]
        exact fun h => hne (SetLike.coe_injective (by simpa using h)))
    obtain ⟨V, hzV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f z
      (MMP.Resolution.Bridges.finite_preimage_singleton_of_topologicalKrullDim_le f z (H z hzc))
    exact hz (Opens.mem_iSup.2 ⟨⟨V, hV⟩, hzV⟩)
  haveI : IsFinite f := IsZariskiLocalAtTarget.of_iSup_eq_top (P := @AlgebraicGeometry.IsFinite) _ hcov
    fun V => V.2
  apply hnt
  let ιa := {U : Z.Opens // IsAffineOpen U}
  have hcova : ⨆ U : ιa, U.1 = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
    exact Opens.mem_iSup.2 ⟨⟨U, hU⟩, hzU⟩
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (f := f) _ hcova fun U => (isIso_morphismRestrict_iff_isIso_app f U.2).2 (hf.isIso_app U.1)

/-- **The case of a curve.** A proper curve `T` in a closed fibre of dimension at most one, on
which `K + B` is negative, is a rational curve with `-(K + B) · T ≤ 2`. -/
private theorem isRationalCurve_and_neg_intersectionNumber_le_two {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hklt : IsKltPair sX n K B) (hB : 0 ≤ B) {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : IsContraction sX sZ f) (z : Z)
    (hz : IsClosed ({z} : Set Z)) (hfib : topologicalKrullDim (f ⁻¹' {z}) ≤ 1)
    (T : ProperCurve sX) (hTz : closure ({T.point} : Set X) ⊆ f ⁻¹' {z})
    (hneg : (Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 < 0) :
    IsRationalCurve sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) ∧
      -(Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 ≤ 2 := by
  haveI : AlgebraicGeometry.IsCurve ℂ (T.ι ≫ sX) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := T.dim_eq }
  haveI := hf.isNormalVariety_target.1
  have hrange : Set.range T.ι ⊆ f ⁻¹' {z} := by
    rintro _ ⟨c, rfl⟩
    apply hTz
    have : T.ι c ∈ Set.range T.ι := ⟨c, rfl⟩
    unfold ProperCurve.ι curveSubschemeAtι at this
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  have hsub := MMP.Fourfold.invertibleCurveDegree_relativeDifferentials_normalization_le_intersectionNumber
    sX hklt hB sZ f hf.comp_eq hf.isProjectiveMorphism z hz hfib T.ι hrange
  set ν := normalizationOverField ℂ (T.ι ≫ sX) with hν
  set g := ν ≫ T.ι ≫ sX with hg
  haveI : Smooth g := (normalizationModel' ℂ (T.ι ≫ sX)).smooth_structureMap
  haveI : AlgebraicGeometry.IsCurve ℂ g := (normalizationModel' ℂ (T.ι ≫ sX)).isCurve
  haveI : IsProper g := isProper_normalizationOverField_comp ℂ (T.ι ≫ sX)
  have hcot := MMP.invertibleCurveDegree_relativeDifferentials_eq_of_isAlgClosed g
  set h := Module.finrank ℂ (structureSheafCohomology g 1) with hh
  have key : (((2 * (h : ℤ) - 2 : ℤ)) : ℚ) ≤
      (Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 := by
    convert hsub using 2
    exact hcot.symm
  have h0 : h = 0 := by
    by_contra h0
    have : (1 : ℚ) ≤ h := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    push_cast at key
    linarith
  refine ⟨?_, ?_⟩
  · haveI : IsIntegral (normalizationSchemeOverField ℂ (T.ι ≫ sX)) :=
      (normalizationModel' ℂ (T.ι ≫ sX)).isCurve.toIsIntegral
    have hdimN : topologicalKrullDim (normalizationSchemeOverField ℂ (T.ι ≫ sX)) = 1 :=
      AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := ℂ) (f := g)
    obtain ⟨-, hgen0, -⟩ := MMP.Mori.arithmeticGenus_eq_finrank_cohomologyOverField_one g
      hdimN.le
    obtain ⟨-, hiff⟩ := MMP.Mori.arithmeticGenus_nonneg_and_eq_zero_iff g hdimN
    have hfin : Module.finrank ℂ
        (cohomologyOverField ℂ g (SheafOfModules.unit _) 1) = 0 := by
      rw [← h0, hh]
      exact (LinearEquiv.finrank_eq
        (structureSheafCohomologyIsoCohomologyOverField ℂ g 1).toLinearEquiv).symm
    obtain ⟨e, he⟩ := hiff.1 (by rw [hgen0, hfin]; rfl)
    haveI : IsFinite ν := isFinite_normalizationOverField ℂ (T.ι ≫ sX)
    have hbir : AlgebraicGeometry.IsBirational (e.hom ≫ ν) :=
      (isBirational_of_iso e).comp (Scheme.isBirational_normalization T.scheme _)
    haveI : IsIntegral (projectiveLine ℂ) := IsIntegral.of_isIso e.inv
    haveI : Finite (irreducibleComponents (projectiveLine ℂ)) := by
      rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
    haveI : Finite (irreducibleComponents T.scheme) := by
      rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
    obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational _ hbir
      (Or.inl ⟨inferInstance, inferInstance⟩)
    refine ⟨⟨inferInstance, T.dim_eq⟩, inferInstance, e.hom ≫ ν, ?_, inferInstance,
      MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso⟩
    simpa [g] using he
  · rw [h0] at key
    push_cast at key
    linarith

/-- **The slope curve when `2 ≤ r < n`.** Embed `X` by a high power `L^m` of an ample sheaf and
cut the normalization `V` of `E = {η}⁻` by `r - 1` general hyperplanes. The cut `Cᵛ` is a smooth
curve in the smooth locus `U` of `V` (maximal-fibre weak subadjunction), it maps birationally to
the cut `C` of `E`, and adjunction on `U` gives `2g(Cᵛ) - 2 = K_U · Cᵛ + (r - 1) m (L · Cᵛ) > 0`
since `K_U · Cᵛ ≥ -c (L · Cᵛ)` for a constant `c` (global generation of `ω_U ⊗ L^c`) and
`m (r - 1) > c`. Weak subadjunction `K_U · Cᵛ ≤ (K + B) · C` gives the slope bound. -/
private theorem exists_slope_curve_of_lt
    (hpoly : ∀ {K : ℕ} (U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K)).Opens),
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K))) →
      ∃ Q : MvPolynomial (Fin (K + 1)) ℂ, Q ≠ 0 ∧
        ∀ (c : Fin (K + 1) → ℂ) (hc : c ≠ 0), MvPolynomial.eval c Q ≠ 0 →
          MMP.Threefold.Bridges.dualPoint c hc ∈ U)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hklt : IsKltPair sX n K B) (hB : 0 ≤ B) {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} (hf : IsContraction sX sZ f) (z : Z)
    (η : X) (hηF : closure ({η} : Set X) ⊆ f ⁻¹' {z}) {r : ℕ} (hr2 : 2 ≤ r) (hrn : r + 1 ≤ n)
    (hdimE : topologicalKrullDim (curveSubschemeAt η) = r)
    (hfib : topologicalKrullDim (f ⁻¹' {z}) = r) {N : ℕ} (hN : 0 < N) {EX : Divisor X}
    (hEXc : EX.IsCartier)
    (hEX : Divisor.toQDivisor EX = (N : ℤ) • -(Divisor.toQDivisor K + B))
    (hEXamp : MMP.Flips.IsRelativelyAmpleCartier f EX) :
    haveI := hEXc.isInvertibleModule_divisorialSheaf
    ∃ (U : (normalizationSchemeOverField ℂ (curveSubschemeAtι η ≫ sX)).Opens)
      (_ : SmoothOfRelativeDimension r
        (U.ι ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫ curveSubschemeAtι η ≫ sX))
      (C : Scheme.{0}) (j : C ⟶ U.toScheme) (_ : IsClosedImmersion j)
      (_ : AlgebraicGeometry.IsCurve ℂ
        (j ≫ U.ι ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫ curveSubschemeAtι η ≫ sX))
      (_ : AlgebraicGeometry.IsProjectiveVariety ℂ
        (j ≫ U.ι ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫ curveSubschemeAtι η ≫ sX))
      (_ : Smooth
        (j ≫ U.ι ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫ curveSubschemeAtι η ≫ sX)),
      1 ≤ genus
        (j ≫ U.ι ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫ curveSubschemeAtι η ≫ sX) ∧
      haveI : Stacks.Ample.IsInvertibleModule U.toScheme
          (Scheme.Hom.relativeDifferentialForms (U.ι ≫ normalizationOverField ℂ
            (curveSubschemeAtι η ≫ sX) ≫ curveSubschemeAtι η ≫ sX) r) :=
        Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ normalizationOverField ℂ
          (curveSubschemeAtι η ≫ sX) ≫ curveSubschemeAtι η ≫ sX) r
      haveI : IsProper ((j ≫ U.ι) ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫
          curveSubschemeAtι η ≫ sX) := by rw [Category.assoc]; infer_instance
      MMP.Mori.degreeOn ℂ (U.ι ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫
          curveSubschemeAtι η ≫ sX) j
          (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := ℂ)
            (f := j ≫ U.ι ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫
              curveSubschemeAtι η ≫ sX)).le
          (Scheme.Hom.relativeDifferentialForms (U.ι ≫ normalizationOverField ℂ
            (curveSubschemeAtι η ≫ sX) ≫ curveSubschemeAtι η ≫ sX) r) < 0 ∧
        (MMP.Mori.degreeOn ℂ (normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫
            curveSubschemeAtι η ≫ sX) (j ≫ U.ι)
            (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := ℂ)
              (f := j ≫ U.ι ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫
                curveSubschemeAtι η ≫ sX)).le
            ((Scheme.Modules.pullback (normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫
              curveSubschemeAtι η)).obj EX.divisorialSheaf) : ℚ) ≤
          N * -(MMP.Mori.degreeOn ℂ (U.ι ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫
            curveSubschemeAtι η ≫ sX) j
            (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := ℂ)
              (f := j ≫ U.ι ≫ normalizationOverField ℂ (curveSubschemeAtι η ≫ sX) ≫
                curveSubschemeAtι η ≫ sX)).le
            (Scheme.Hom.relativeDifferentialForms (U.ι ≫ normalizationOverField ℂ
              (curveSubschemeAtι η ≫ sX) ≫ curveSubschemeAtι η ≫ sX) r) : ℚ) := by
  obtain ⟨d, rfl⟩ : ∃ d, r = d + 2 := ⟨r - 2, by omega⟩
  haveI := hf.isNormalVariety_target.1
  -- the component `E` and its normalization `V`
  set i := curveSubschemeAtι η with hi
  haveI : IsIntegral (curveSubschemeAt η) :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure η
  haveI hEvar : AlgebraicGeometry.IsVariety ℂ (i ≫ sX) := { toIsIntegral := inferInstance }
  have hEproj : IsProjectiveMorphism (i ≫ sX) := by
    obtain ⟨N', φ, hφ, hφs⟩ := (‹AlgebraicGeometry.IsProjectiveVariety ℂ sX›).isProjective
    haveI := hφ
    exact ⟨N', i ≫ φ, inferInstance, by rw [Category.assoc, hφs]⟩
  set ν := normalizationOverField ℂ (i ≫ sX) with hν
  haveI : IsFinite ν := isFinite_normalizationOverField ℂ (i ≫ sX)
  haveI hVvar : AlgebraicGeometry.IsVariety ℂ (ν ≫ i ≫ sX) :=
    isVariety_normalizationOverField ℂ (i ≫ sX)
  haveI : IsProper (i ≫ sX) := isProper_of_isProjectiveMorphism _ hEproj
  haveI hVproj : AlgebraicGeometry.IsProjectiveVariety ℂ (ν ≫ i ≫ sX) :=
    { isProjective := (isProjective_iff_isProjectiveMorphism_of_isAffine _).mp
        ((isProper_and_isProjective_normalizationOverField ℂ (i ≫ sX)).2
          ((isProjective_iff_isProjectiveMorphism_of_isAffine _).mpr hEproj)) }
  haveI : IsNormal (normalizationSchemeOverField ℂ (i ≫ sX)) :=
    Scheme.isNormal_normalizationScheme _ _
  haveI : IsLocallyNoetherian (normalizationSchemeOverField ℂ (i ≫ sX)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ν ≫ i ≫ sX)
  haveI : CompactSpace (normalizationSchemeOverField ℂ (i ≫ sX)) :=
    QuasiCompact.compactSpace_of_compactSpace (ν ≫ i ≫ sX)
  haveI : IsIntegral (normalizationSchemeOverField ℂ (i ≫ sX)) := hVvar.toIsIntegral
  haveI : IsNoetherian (normalizationSchemeOverField ℂ (i ≫ sX)) := {}
  set g := ν ≫ i with hgdef
  haveI : IsFinite g := by rw [hgdef]; infer_instance
  haveI := hEXc.isInvertibleModule_divisorialSheaf
  have hEz : Set.range i ⊆ f ⁻¹' {z} := by
    rw [hi, range_curveSubschemeAtι η]; exact hηF
  have hgz : ∀ v, f (g v) = z := fun v => hEz ⟨ν v, rfl⟩
  have hMamp := isAmple_pullback_of_isRelativelyAmpleCartier hEXamp g z hgz
  have hdimV : topologicalKrullDim (normalizationSchemeOverField ℂ (i ≫ sX)) =
      ((d + 2 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_normalizationSchemeOverField ℂ (i ≫ sX)).trans hdimE
  -- the smooth locus `U` of `V`
  set sV := ν ≫ i ≫ sX with hsV
  set U := smoothLocus sV with hU
  have hUsm : SmoothOfRelativeDimension (d + 2) (U.ι ≫ sV) :=
    smoothOfRelativeDimension_of_le_smoothLocus sV hdimV U le_rfl
  haveI := hUsm
  haveI : Nonempty U := ⟨⟨genericPoint _, MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus'⟩⟩
  haveI hUvar : AlgebraicGeometry.IsVariety ℂ (U.ι ≫ sV) :=
    Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι ℂ sV U
  have hdimU : topologicalKrullDim U = ((d + 2 : ℕ) : WithBot ℕ∞) :=
    (Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens ℂ sV U).trans hdimV
  haveI : Smooth (U.ι ≫ sV) := SmoothOfRelativeDimension.smooth (d + 2) _
  -- an ample `L` on `X`, its pullback `L₁` to `U`, and the constant of the genus bound
  obtain ⟨L, hLinv, hL⟩ := exists_isAmple_of_isProjectiveMorphism sX
    (‹AlgebraicGeometry.IsProjectiveVariety ℂ sX›).isProjective
  haveI : Stacks.Ample.IsInvertibleModule U.toScheme ((Scheme.Modules.pullback (U.ι ≫ g)).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (U.ι ≫ g) L
  set L₁ : U.toScheme.Modules := (Scheme.Modules.pullback (U.ι ≫ g)).obj L with hL₁def
  have hL₁ : Stacks.Ample.IsAmple U.toScheme L₁ := by
    have := MMP.Mori.isInvertible_pullback_obj g L
    have h1 := isAmple_pullback_of_isFinite g L
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hL)
    have h2 := Stacks.AmpleRestrict.isAmple_pullback_ι_of_isNoetherian U _ h1
    haveI : SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2
        ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback U.ι).obj L) :=
      MMP.Mori.isInvertible_pullback_obj U.ι ((Scheme.Modules.pullback g).obj L)
    exact (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp
      (Scheme.Modules.isAmple_of_iso ((Scheme.Modules.pullbackComp _ _).app L) h2)
  haveI := Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sV) (d + 2)
  obtain ⟨n₁, hn₁⟩ := exists_neg_mul_degreeOn_le_of_isAmple (U.ι ≫ sV) L₁
    (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) ((d + 2 : ℕ) : ℤ)) hL₁
  -- the embedding by `L^m`, `m` large
  obtain ⟨m₀, hm₀, hemb⟩ := exists_isClosedImmersion_twistOne_iso sX
    (‹AlgebraicGeometry.IsProjectiveVariety ℂ sX›).isProjective L hL
  set m := max m₀ (n₁ + 1) with hm
  obtain ⟨N', φ, hφ, hφs, ⟨eφ⟩⟩ := hemb m (le_max_left _ _)
  haveI := hφ
  -- maximal-fibre weak subadjunction for the embedding `φ`
  have hcard₀ :=
    MMP.Fourfold.exists_invertibleCurveDegree_canonicalSheaf_normalization_le_intersectionNumber
      (k := ℂ) sX hklt hB sZ f hf.comp_eq hf.isProjectiveMorphism z i hEz (by omega) hrn hdimE
      hfib φ hφs
  rw [show d + 2 - 1 = d + 1 from rfl] at hcard₀
  obtain ⟨P₁, hP₁, hcard⟩ := hcard₀
  -- the locus `O ⊆ E` over which `ν` is an isomorphism; its complement has dimension `≤ r - 1`
  haveI : IsLocallyNoetherian (curveSubschemeAt η) :=
    LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  haveI : CompactSpace (curveSubschemeAt η) := QuasiCompact.compactSpace_of_compactSpace (i ≫ sX)
  haveI : IsNoetherian (curveSubschemeAt η) := {}
  let O : (curveSubschemeAt η).Opens :=
    ⟨regularLocus (curveSubschemeAt η), MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType (i ≫ sX)⟩
  haveI hνO : IsIso (ν ∣_ O) :=
    isIso_morphismRestrict_normalization_of_subset_regularLocus _ O le_rfl
  have hηO : genericPoint (curveSubschemeAt η) ∈ (O : Set (curveSubschemeAt η)) :=
    MMP.Flips.isRegularLocalRing_stalk_of_coheight_eq_zero (Order.coheight_eq_zero.2
      fun y _ => (genericPoint_spec (curveSubschemeAt η)).specializes (Set.mem_univ y))
  have hdimO : topologicalKrullDim ↥((O : Set (curveSubschemeAt η))ᶜ) ≤
      ((d + 1 : ℕ) : WithBot ℕ∞) := by
    have hle := Topology.topologicalKrullDim_add_one_le_of_ne_univ
      (S := (O : Set (curveSubschemeAt η))ᶜ) O.isOpen.isClosed_compl
      (fun h => (h ▸ Set.mem_univ (genericPoint (curveSubschemeAt η)) :
        genericPoint (curveSubschemeAt η) ∈ (O : Set (curveSubschemeAt η))ᶜ) hηO)
    rw [hdimE] at hle
    exact withBot_le_of_add_one_le hle
  haveI : IsNoetherian (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N')) :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (Stacks.ProjectiveCohomology.projModelToSpec ℂ N'),
      __ := QuasiCompact.compactSpace_of_compactSpace
        (Stacks.ProjectiveCohomology.projModelToSpec ℂ N') }
  have hcons : ∀ {W : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N'))}, IsClosed W →
      Topology.IsConstructible W := fun hW => Topology.isConstructible_compl.1
    ((TopologicalSpace.NoetherianSpace.isCompact _).isConstructible hW.isOpen_compl)
  -- the dimension count for the cuts of the image of `E ∖ O`
  set W₀ : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N')) :=
    (i ≫ φ) '' (O : Set (curveSubschemeAt η))ᶜ with hW₀
  have hW₀c : IsClosed W₀ := (i ≫ φ).isClosedEmbedding.isClosedMap _ O.isOpen.isClosed_compl
  obtain ⟨P₂, hP₂, hcut⟩ := MMP.Threefold.Bridges.exists_polynomial_inter_hyperplanes (k := ℂ)
    (fun _ : Unit => W₀) (fun _ => hcons hW₀c) (d + 1)
  -- the general complete intersection
  obtain ⟨c, hcP, hred, hcurve⟩ := exists_completeIntersection_curve hpoly d (U.ι ≫ sV) hdimU
    (U.ι ≫ ν ≫ i ≫ φ) (by simp only [hsV, Category.assoc, hφs]) (i ≫ sX) (i ≫ φ)
    (by rw [Category.assoc, hφs])
    (P₁ * P₂) (mul_ne_zero hP₁ hP₂)
  rw [map_mul] at hcP
  have hc₁ := left_ne_zero_of_mul hcP
  have hc₂ := right_ne_zero_of_mul hcP
  have hcardc := hcard c hc₁
  -- name the cut `IC` without rewriting the whole context
  generalize hIC' : (⨆ j, MMP.Threefold.Bridges.hyperplaneSection (i ≫ φ) (c j) :
    (curveSubschemeAt η).IdealSheafData) = IC at hcardc hred
  have hIC : IC = ⨆ j, MMP.Threefold.Bridges.hyperplaneSection (i ≫ φ) (c j) := hIC'.symm
  obtain ⟨hICdim, hICνdim, hsm, hsmooth, hω, hineq⟩ := hcardc
  set ICν := IC.comap ν with hICν
  -- `π : Cᵛ ⟶ C` is a surjective base change of `ν`
  set π := Scheme.IdealSheafData.subschemeMap ICν IC ν (IC.le_map_comap ν) with hπdef
  have hπ : π ≫ IC.subschemeι = ICν.subschemeι ≫ ν :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have sq : IsPullback ICν.subschemeι π ν IC.subschemeι :=
    isPullback_of_isClosedImmersion _ _ π ν hπ.symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])
  haveI hπs : Surjective π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) sq inferInstance
  -- `C` meets `O`, by the dimension count
  have hO : ∃ y : IC.subscheme, IC.subschemeι y ∈ (O : Set (curveSubschemeAt η)) := by
    haveI : Nonempty IC.subscheme := nonempty_of_topologicalKrullDim_eq (m := 1) hICdim
    by_contra hno
    push Not at hno
    -- `C` maps into the cut `W₀ ∩ H_{c₀} ∩ ⋯ ∩ H_{c_d}` of the image of `E ∖ O`
    set Hc := W₀ ∩ ⋂ j, ((Stacks.ProjectiveSpace.hyperplane
      (MMP.Threefold.Bridges.linearForm (c j))).support :
        Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N'))) with hHc
    have hmapsto : ∀ y : IC.subscheme, (IC.subschemeι ≫ i ≫ φ) y ∈ Hc := by
      intro y
      refine ⟨⟨IC.subschemeι y, hno y, rfl⟩, Set.mem_iInter.2 fun j => ?_⟩
      have hy : IC.subschemeι y ∈ ((⨆ j, MMP.Threefold.Bridges.hyperplaneSection (i ≫ φ) (c j) :
          (curveSubschemeAt η).IdealSheafData).support : Set (curveSubschemeAt η)) := by
        rw [← hIC, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y, rfl⟩
      rw [Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.coe_iInf,
        Set.mem_iInter] at hy
      have hyj := hy j
      rw [MMP.Threefold.Bridges.hyperplaneSection, Scheme.IdealSheafData.support_comap] at hyj
      exact hyj
    obtain ⟨hlt, hge⟩ := hcut c hc₂ ()
    have hW₀dim : topologicalKrullDim W₀ ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
      have hemb : Topology.IsEmbedding
          (fun x : ↥((O : Set (curveSubschemeAt η))ᶜ) => (i ≫ φ) x.1) :=
        (i ≫ φ).isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
      rw [hW₀, Set.image_eq_range,
        ← IsHomeomorph.topologicalKrullDim_eq _ hemb.toHomeomorph.isHomeomorph]
      exact hdimO
    by_cases hc : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim W₀
    · obtain ⟨-, hsum⟩ := hge hc
      have hHc0 : topologicalKrullDim Hc ≤ 0 :=
        withBot_le_zero_of_add_le (m := d + 1) (hsum.le.trans hW₀dim)
      have hind : Topology.IsInducing
          (fun y : IC.subscheme => (⟨(IC.subschemeι ≫ i ≫ φ) y, hmapsto y⟩ : Hc)) :=
        (IC.subschemeι ≫ i ≫ φ).isClosedEmbedding.isInducing.codRestrict hmapsto
      have h1 := hind.topologicalKrullDim_le.trans hHc0
      rw [hICdim] at h1
      exact absurd h1 (by decide)
    · push Not at hc
      have hempty := hlt hc
      obtain ⟨y⟩ : Nonempty IC.subscheme := inferInstance
      have := hmapsto y
      rw [hHc, hempty] at this
      exact this
  obtain ⟨y₀, hy₀⟩ := hO
  -- the cut on `U` is the preimage of `Cᵛ`, which lies in `U`
  have hJ : (⨆ j, MMP.Threefold.Bridges.hyperplaneSection (U.ι ≫ ν ≫ i ≫ φ) (c j)) =
      ICν.comap U.ι := by
    rw [hICν, hIC, iSup_hyperplaneSection_comp, iSup_hyperplaneSection_comp]
  have hsm' : Set.range ICν.subschemeι ⊆ (U : Set (normalizationSchemeOverField ℂ (i ≫ sX))) :=
    hsm
  have hne : ((⨆ j, MMP.Threefold.Bridges.hyperplaneSection (U.ι ≫ ν ≫ i ≫ φ) (c j)).support :
      Set U.toScheme).Nonempty := by
    obtain ⟨v, hv⟩ := (inferInstance : Surjective ν).surj (IC.subschemeι y₀)
    have hvC : v ∈ Set.range ICν.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hICν, Scheme.IdealSheafData.support_comap]
      change ν v ∈ (IC.support : Set _)
      rw [hv, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨y₀, rfl⟩
    obtain ⟨u, hu⟩ : v ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hsm' hvC
    refine ⟨u, ?_⟩
    rw [hJ, Scheme.IdealSheafData.support_comap]
    change U.ι u ∈ (ICν.support : Set _)
    rw [hu, ← Scheme.IdealSheafData.range_subschemeι]
    exact hvC
  obtain ⟨C, ι, hι, hvarC, hsmC, hC1, hkerC, hdegC⟩ := hcurve hne
  haveI := hι
  haveI := hvarC
  haveI := hsmC
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_ker_eq_comap U ICν hsm' ι (hkerC.trans hJ)
  -- integrality and dimensions of `C` and `Cᵛ`
  haveI : IsIntegral C := hvarC.toIsIntegral
  haveI : IsIntegral ICν.subscheme := IsIntegral.of_isIso e.hom
  haveI : IrreducibleSpace IC.subscheme :=
    Function.Surjective.irreducibleSpace π.continuous hπs.surj
  haveI : IsReduced IC.subscheme := hred
  haveI : IsIntegral IC.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hICν1 : topologicalKrullDim ICν.subscheme = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).symm.trans hC1
  -- properness
  haveI : IsClosedImmersion (ι ≫ U.ι) := by rw [← he]; infer_instance
  haveI : IsProper (ι ≫ U.ι ≫ sV) := by rw [← Category.assoc]; infer_instance
  haveI : IsProper ((ι ≫ U.ι) ≫ sV) := inferInstance
  haveI : IsProper (ICν.subschemeι ≫ sV) := inferInstance
  haveI : IsProper (IC.subschemeι ≫ i ≫ sX) := inferInstance
  haveI : IsProper ((IC.subschemeι ≫ i) ≫ sX) := inferInstance
  haveI : IsProper ((ICν.subschemeι ≫ ν) ≫ i ≫ sX) := by rw [Category.assoc]; infer_instance
  haveI : IsProper (ICν.subschemeι ≫ ν ≫ i ≫ sX) := inferInstance
  haveI : IsProper ((ICν.subschemeι ≫ g) ≫ sX) := by rw [hgdef]; simp only [Category.assoc]; infer_instance
  -- `δ = deg_C 𝒪(E_X) = deg_{Cᵛ} g^* 𝒪(E_X)`
  set δ := degreeOn ℂ sX (IC.subschemeι ≫ i) hICdim.le EX.divisorialSheaf with hδ
  have hδV : degreeOn ℂ sV (ι ≫ U.ι) hC1.le ((Scheme.Modules.pullback g).obj EX.divisorialSheaf) =
      δ := by
    haveI := MMP.Mori.isInvertible_pullback_obj g EX.divisorialSheaf
    haveI := MMP.Mori.isInvertible_pullback_obj i EX.divisorialSheaf
    rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp ℂ sV (ι ≫ U.ι) ICν.subschemeι hC1.le
      hICν1.le e he, degreeOn_pullback_eq_degreeOn_comp sV sX g ICν.subschemeι
        (by rw [hgdef, Category.assoc]) hICν1.le,
      MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp ℂ sX (ICν.subschemeι ≫ g)
        ((ICν.subschemeι ≫ ν) ≫ i) hICν1.le hICν1.le (Iso.refl _)
        (by rw [Iso.refl_hom, Category.id_comp, hgdef, Category.assoc]),
      ← degreeOn_pullback_eq_degreeOn_comp (i ≫ sX) sX i (ICν.subschemeι ≫ ν) rfl hICν1.le,
      degreeOn_comp_comap_eq_of_isIso_morphismRestrict (i ≫ sX) ν O IC hICdim hICν1
        ⟨y₀, hy₀⟩, degreeOn_pullback_eq_degreeOn_comp (i ≫ sX) sX i IC.subschemeι rfl hICdim.le]
  -- `κ = K_U · Cᵛ`, the degree in the weak subadjunction inequality
  set F := Scheme.Hom.relativeDifferentialForms (U.ι ≫ sV) ((d + 2 : ℕ) : ℤ) with hF
  set κ := degreeOn ℂ (U.ι ≫ sV) ι hC1.le F with hκ
  set t := IsOpenImmersion.lift (smoothLocus sV).ι ICν.subschemeι
    (hsm.trans_eq (Scheme.Opens.range_ι _).symm) with ht
  have ht' : t ≫ U.ι = ICν.subschemeι := IsOpenImmersion.lift_fac _ _ _
  have het : e.hom ≫ t = ι := by
    rw [← cancel_mono U.ι, Category.assoc, ht', he]
  haveI : IsProper (t ≫ U.ι ≫ sV) := by rw [← Category.assoc, ht']; infer_instance
  have hκcard : κ = @invertibleCurveDegree ℂ _ _ (ICν.subschemeι ≫ ν ≫ i ≫ sX) _ hICνdim
      ((Scheme.Modules.pullback t).obj (canonicalSheaf (ν ≫ i ≫ sX) (d + 2))) hω := by
    rw [hκ, MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp ℂ (U.ι ≫ sV) ι t hC1.le hICν1.le e het,
      degreeOn_eq_invertibleCurveDegree]
    exact invertibleCurveDegree_congr_hom (by rw [← Category.assoc, ht']) _
  -- `(K + B) · C = -δ / N`
  have hEneg : Divisor.toQDivisor (-EX) = ((N : ℕ) : ℤ) • (Divisor.toQDivisor K + B) := by
    rw [map_neg, hEX, smul_neg, neg_neg]
  have hKB : (Divisor.toQDivisor K + B).intersectionNumber ℂ sX (IC.subschemeι ≫ i) hICdim.le
      hklt.1.2.2 = -(δ : ℚ) / N := by
    rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX (IC.subschemeι ≫ i) hICdim.le _ hklt.1.2.2 hN
      (-EX) hEXc.neg hEneg]
    have h0 := Divisor.degreeOn_add ℂ sX (IC.subschemeι ≫ i) hICdim.le EX (-EX) hEXc hEXc.neg
    rw [Divisor.degreeOn_congr (add_neg_cancel EX) _ Divisor.isCartier_zero,
      Divisor.degreeOn_zero'] at h0
    have h1 : (-EX).degreeOn ℂ sX (IC.subschemeι ≫ i) hICdim.le hEXc.neg = -δ := by
      have : EX.degreeOn ℂ sX (IC.subschemeι ≫ i) hICdim.le hEXc = δ := rfl
      linarith
    rw [h1]
    push_cast
    ring
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hκle : (κ : ℚ) ≤ -(δ : ℚ) / N := by
    rw [← hKB, hκcard]
    exact hineq
  -- `δ > 0`, the pullback of `E_X` to `V` being ample
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ U.ι ≫ sV)
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (ι ≫ U.ι ≫ sV)
  haveI : IsNoetherian C := {}
  have hδpos : 0 < δ := by
    rw [← hδV, degreeOn_eq_invertibleCurveDegree]
    haveI := MMP.Mori.isInvertible_pullback_obj g EX.divisorialSheaf
    exact invertibleCurveDegree_pos_of_isAmple_of_not_subsingleton_range ℂ ((ι ≫ U.ι) ≫ sV) hC1
      (ι ≫ U.ι) (not_subsingleton_range_of_topologicalKrullDim_eq_one (ι ≫ U.ι)
        (ι ≫ U.ι).isClosedEmbedding.injective hC1) _ hMamp
  -- the genus
  have hgenus : 1 ≤ genus (ι ≫ U.ι ≫ sV) := by
    have hcomb := hdegC inferInstance
    haveI hCcurve' : AlgebraicGeometry.IsCurve ℂ (ι ≫ U.ι ≫ sV) :=
      { topologicalKrullDim_eq_one := hC1 }
    have hcot := MMP.invertibleCurveDegree_relativeDifferentials_eq_of_isAlgClosed (ι ≫ U.ι ≫ sV)
    have h2g : (2 * (genus (ι ≫ U.ι ≫ sV) : ℤ) - 2) = κ + ((d + 1 : ℕ) : ℤ) *
        degreeOn ℂ (U.ι ≫ sV) ι hC1.le ((Scheme.Modules.pullback (U.ι ≫ ν ≫ i ≫ φ)).obj
          (MMP.Threefold.Bridges.twistOne ℂ N')) := by
      rw [genus_eq_finrank_structureSheafCohomology]
      exact hcot.symm.trans hcomb
    -- the hyperplane degree is `m · (L · Cᵛ)`
    set lam := degreeOn ℂ (U.ι ≫ sV) ι hC1.le L₁ with hlam
    haveI : IsProper ((ι ≫ U.ι ≫ g) ≫ sX) := by
      rw [hgdef]; simp only [Category.assoc]; infer_instance
    have hψ : degreeOn ℂ (U.ι ≫ sV) ι hC1.le ((Scheme.Modules.pullback (U.ι ≫ ν ≫ i ≫ φ)).obj
        (MMP.Threefold.Bridges.twistOne ℂ N')) = (m : ℤ) * lam := by
      haveI := MMP.Mori.isInvertible_pullback_obj φ (MMP.Threefold.Bridges.twistOne ℂ N')
      have e₃ : (Scheme.Modules.pullback (U.ι ≫ ν ≫ i ≫ φ)).obj
          (MMP.Threefold.Bridges.twistOne ℂ N') ≅ (Scheme.Modules.pullback (U.ι ≫ g)).obj
            (Stacks.Ample.tensorPowModule X L (m : ℤ)) :=
        (Scheme.Modules.pullbackCongr (by rw [hgdef]; simp only [Category.assoc])).app _ ≪≫
          ((Scheme.Modules.pullbackComp (U.ι ≫ g) φ).app _).symm ≪≫
          (Scheme.Modules.pullback (U.ι ≫ g)).mapIso eφ.symm
      haveI := MMP.Mori.isInvertible_pullback_obj (U.ι ≫ g)
        (Stacks.Ample.tensorPowModule X L (m : ℤ))
      have hUg : (U.ι ≫ g) ≫ sX = U.ι ≫ sV := by rw [hgdef, hsV]; simp only [Category.assoc]
      rw [degreeOn_eq_of_iso ℂ (U.ι ≫ sV) ι hC1.le e₃,
        degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sV) sX (U.ι ≫ g) ι hUg hC1.le,
        degreeOn_tensorPowModule_natCast', hlam,
        degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sV) sX (U.ι ≫ g) ι hUg hC1.le]
    have hlampos : 0 < lam := by
      rw [hlam, degreeOn_eq_invertibleCurveDegree]
      exact invertibleCurveDegree_pos_of_isAmple_of_not_subsingleton_range ℂ (ι ≫ U.ι ≫ sV) hC1
        ι (not_subsingleton_range_of_topologicalKrullDim_eq_one ι ι.isClosedEmbedding.injective hC1)
        L₁ ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hL₁)
    have hn : -((n₁ : ℤ) * lam) ≤ κ := hn₁ ι hC1.le
    have hm1 : n₁ + 1 ≤ m := le_max_right _ _
    rw [hψ] at h2g
    have hm1' : ((n₁ : ℤ) + 1) ≤ ((d + 1 : ℕ) : ℤ) * (m : ℤ) := by
      have : ((n₁ : ℤ) + 1) ≤ (m : ℤ) := by exact_mod_cast hm1
      exact this.trans (le_mul_of_one_le_left (Int.natCast_nonneg m) (by omega))
    have hpos : (0 : ℤ) < 2 * (genus (ι ≫ U.ι ≫ sV) : ℤ) - 2 := by
      have h3 : ((n₁ : ℤ) + 1) * lam ≤ ((d + 1 : ℕ) : ℤ) * (m : ℤ) * lam :=
        mul_le_mul_of_nonneg_right hm1' hlampos.le
      rw [h2g]
      linarith only [h3, hn, hlampos]
    omega
  haveI hCcurve : AlgebraicGeometry.IsCurve ℂ (ι ≫ U.ι ≫ sV) := { topologicalKrullDim_eq_one := hC1 }
  have hCproj : AlgebraicGeometry.IsProjectiveVariety ℂ (ι ≫ U.ι ≫ sV) := by
    obtain ⟨N'', φ', hφ', hφs'⟩ := hVproj.isProjective
    haveI := hφ'
    exact { isProjective := ⟨N'', (ι ≫ U.ι) ≫ φ', inferInstance, by
      simp only [Category.assoc, hφs']⟩ }
  refine ⟨U, hUsm, C, ι, hι, hCcurve, hCproj, hsmC, hgenus, ?_, ?_⟩
  · have : (κ : ℚ) < 0 := hκle.trans_lt (by
      rw [neg_div]; exact neg_neg_of_pos (div_pos (by exact_mod_cast hδpos) hNq))
    exact_mod_cast this
  · have hδV' : degreeOn ℂ sV (ι ≫ U.ι) hC1.le
        ((Scheme.Modules.pullback g).obj EX.divisorialSheaf) = δ := hδV
    rw [show (degreeOn ℂ sV (ι ≫ U.ι) _ ((Scheme.Modules.pullback g).obj EX.divisorialSheaf) : ℚ) =
      δ from by exact_mod_cast hδV']
    rw [le_div_iff₀ hNq] at hκle
    change (δ : ℚ) ≤ N * -(κ : ℚ)
    linarith

/-- **The slope curve when `r = n`.** Here the fibre is all of `X`, and `-(K + B)` is ample. Embed
`X` by a high power `L^m` of an ample sheaf and cut it by `n - 1` general hyperplanes. Since `X` is
normal, its singular locus has codimension at least two, so the cut `C` is a smooth curve inside
the smooth locus `U` of `X`; it is not contained in the support of the effective divisor
`N(K + B) - NK`. Adjunction on `U` gives `2g(C) - 2 = K_U · C + (n - 1) m (L · C) > 0`, and
`N K_U · C ≤ N (K + B) · C = -𝒪(E_X) · C < 0`, computed on `U` where every divisor is Cartier. -/
private theorem exists_slope_curve_of_eq
    (hpoly : ∀ {K : ℕ} (U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K)).Opens),
      Dense (U : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ K))) →
      ∃ Q : MvPolynomial (Fin (K + 1)) ℂ, Q ≠ 0 ∧
        ∀ (c : Fin (K + 1) → ℂ) (hc : c ≠ 0), MvPolynomial.eval c Q ≠ 0 →
          MMP.Threefold.Bridges.dualPoint c hc ∈ U)
    {d : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : IsKltPair sX (d + 2) K B) (hB : 0 ≤ B)
    {N : ℕ} (hN : 0 < N) {EX : Divisor X} (hEXc : EX.IsCartier)
    (hEX : Divisor.toQDivisor EX = (N : ℤ) • -(Divisor.toQDivisor K + B))
    (hEXamp : haveI := hEXc.isInvertibleModule_divisorialSheaf
      Scheme.Modules.IsAmple X EX.divisorialSheaf) :
    haveI := hEXc.isInvertibleModule_divisorialSheaf
    ∃ (_ : SmoothOfRelativeDimension (d + 2) ((smoothLocus sX).ι ≫ sX))
      (C : Scheme.{0}) (j : C ⟶ (smoothLocus sX).toScheme) (_ : IsClosedImmersion j)
      (_ : AlgebraicGeometry.IsCurve ℂ (j ≫ (smoothLocus sX).ι ≫ sX))
      (_ : AlgebraicGeometry.IsProjectiveVariety ℂ (j ≫ (smoothLocus sX).ι ≫ sX))
      (_ : Smooth (j ≫ (smoothLocus sX).ι ≫ sX)),
      1 ≤ genus (j ≫ (smoothLocus sX).ι ≫ sX) ∧
      haveI : Stacks.Ample.IsInvertibleModule (smoothLocus sX).toScheme
          (Scheme.Hom.relativeDifferentialForms ((smoothLocus sX).ι ≫ sX) ((d + 2 : ℕ) : ℤ)) :=
        Stacks.Discriminant.isInvertible_relativeDifferentialForms ((smoothLocus sX).ι ≫ sX)
          (d + 2)
      haveI : IsProper ((j ≫ (smoothLocus sX).ι) ≫ sX) := by
        rw [Category.assoc]; infer_instance
      MMP.Mori.degreeOn ℂ ((smoothLocus sX).ι ≫ sX) j
          (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := ℂ)
            (f := j ≫ (smoothLocus sX).ι ≫ sX)).le
          (Scheme.Hom.relativeDifferentialForms ((smoothLocus sX).ι ≫ sX) ((d + 2 : ℕ) : ℤ)) < 0 ∧
        (MMP.Mori.degreeOn ℂ sX (j ≫ (smoothLocus sX).ι)
            (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := ℂ)
              (f := j ≫ (smoothLocus sX).ι ≫ sX)).le EX.divisorialSheaf : ℚ) ≤
          N * -(MMP.Mori.degreeOn ℂ ((smoothLocus sX).ι ≫ sX) j
            (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := ℂ)
              (f := j ≫ (smoothLocus sX).ι ≫ sX)).le
            (Scheme.Hom.relativeDifferentialForms ((smoothLocus sX).ι ≫ sX) ((d + 2 : ℕ) : ℤ)) :
              ℚ) := by
  haveI := hEXc.isInvertibleModule_divisorialSheaf
  have hXn : IsNormalVariety ℂ sX := hklt.1.1
  have hK := hklt.1.2.1
  have hdimX : topologicalKrullDim X = ((d + 2 : ℕ) : WithBot ℕ∞) := hK.1
  haveI : IsNoetherian X := {}
  -- the smooth locus `U`
  set U := smoothLocus sX with hU
  have hUsm : SmoothOfRelativeDimension (d + 2) (U.ι ≫ sX) :=
    smoothOfRelativeDimension_of_le_smoothLocus sX hdimX U le_rfl
  haveI := hUsm
  haveI : Nonempty U :=
    ⟨⟨genericPoint X, MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus' (f := sX)⟩⟩
  haveI : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι (U.isOpen.dense ⟨_, (Classical.arbitrary U).2⟩)
  haveI hUvar : AlgebraicGeometry.IsVariety ℂ (U.ι ≫ sX) :=
    Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι ℂ sX U
  have hdimU : topologicalKrullDim U = ((d + 2 : ℕ) : WithBot ℕ∞) :=
    (Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens ℂ sX U).trans hdimX
  haveI : Smooth (U.ι ≫ sX) := SmoothOfRelativeDimension.smooth (d + 2) _
  have hsmU : IsSmoothScheme (U.ι ≫ sX) := by
    rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, Scheme.Hom.smoothLocus_eq_top_iff]
    infer_instance
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sX)
  have hcU : ∀ D : Divisor U.toScheme, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmU
  -- an ample `L` on `X`, its restriction `L₁` to `U`, and the constant of the genus bound
  obtain ⟨L, hLinv, hL⟩ := exists_isAmple_of_isProjectiveMorphism sX
    (‹AlgebraicGeometry.IsProjectiveVariety ℂ sX›).isProjective
  haveI : Stacks.Ample.IsInvertibleModule U.toScheme ((Scheme.Modules.pullback U.ι).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback U.ι L
  set L₁ : U.toScheme.Modules := (Scheme.Modules.pullback U.ι).obj L with hL₁def
  have hL₁ : Stacks.Ample.IsAmple U.toScheme L₁ :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp
      (Stacks.AmpleRestrict.isAmple_pullback_ι_of_isNoetherian U _
        ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hL))
  haveI := Stacks.Discriminant.isInvertible_relativeDifferentialForms (U.ι ≫ sX) (d + 2)
  obtain ⟨n₁, hn₁⟩ := exists_neg_mul_degreeOn_le_of_isAmple (U.ι ≫ sX) L₁
    (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sX) ((d + 2 : ℕ) : ℤ)) hL₁
  -- the embedding by `L^m`, `m` large
  obtain ⟨m₀, hm₀, hemb⟩ := exists_isClosedImmersion_twistOne_iso sX
    (‹AlgebraicGeometry.IsProjectiveVariety ℂ sX›).isProjective L hL
  set m := max m₀ (n₁ + 1) with hm
  obtain ⟨N', φ, hφ, hφs, ⟨eφ⟩⟩ := hemb m (le_max_left _ _)
  haveI := hφ
  -- the effective divisor `B' = N (K + B) - N K`
  set G : Divisor X := -EX with hGdef
  set B' : Divisor X := G - N • K with hB'def
  have hB'Q : Divisor.toQDivisor B' = (N : ℤ) • B := by
    rw [hB'def, map_sub, map_nsmul, hGdef, map_neg, hEX, smul_neg, neg_neg, smul_add,
      ← natCast_zsmul]
    abel
  have hB'eff : 0 ≤ B' := by
    refine Finsupp.le_def.2 fun E => ?_
    have h := congrArg (fun D : QDivisor X => D E) hB'Q
    simp only [Finsupp.smul_apply, zsmul_eq_mul] at h
    have hBE : (0 : ℚ) ≤ B E := Finsupp.le_def.1 hB E
    have : (0 : ℚ) ≤ (B' E : ℚ) := by
      rw [show ((B' E : ℤ) : ℚ) = Divisor.toQDivisor B' E from rfl, h]
      exact mul_nonneg (by positivity) hBE
    exact_mod_cast this
  -- the dimension counts: the singular locus and the support of `B'`
  set Ssing : Set X := (U : Set X)ᶜ with hSsing
  have hSsingc : IsClosed Ssing := U.isOpen.isClosed_compl
  have hSsingdim : topologicalKrullDim Ssing ≤ (d : WithBot ℕ∞) :=
    topologicalKrullDim_le_of_le_coheight (n := d) (r := 2) sX hdimX hSsingc
      fun y hy => two_le_coheight_of_notMem_smoothLocus hXn hy
  set Sb : Set X := (B'.supp : Set X) with hSb
  have hSbc : IsClosed Sb := B'.supp.isClosed
  have hSbdim : topologicalKrullDim Sb ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_le_of_le_coheight (n := d + 1) (r := 1) sX hdimX hSbc
      fun y hy => one_le_coheight_of_mem_supp hy
  haveI : IsNoetherian (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N')) :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (Stacks.ProjectiveCohomology.projModelToSpec ℂ N'),
      __ := QuasiCompact.compactSpace_of_compactSpace
        (Stacks.ProjectiveCohomology.projModelToSpec ℂ N') }
  have hcons : ∀ {W : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N'))}, IsClosed W →
      Topology.IsConstructible W := fun hW => Topology.isConstructible_compl.1
    ((TopologicalSpace.NoetherianSpace.isCompact _).isConstructible hW.isOpen_compl)
  obtain ⟨Pa, hPa, hcuta⟩ := MMP.Threefold.Bridges.exists_polynomial_inter_hyperplanes (k := ℂ)
    (fun _ : Unit => Set.range φ) (fun _ => hcons φ.isClosedEmbedding.isClosed_range)
    (d + 1)
  obtain ⟨Pb, hPb, hcutb⟩ := MMP.Threefold.Bridges.exists_polynomial_inter_hyperplanes (k := ℂ)
    (fun _ : Unit => φ '' Ssing)
    (fun _ => hcons (φ.isClosedEmbedding.isClosedMap _ hSsingc)) (d + 1)
  obtain ⟨Pc, hPc, hcutc⟩ := MMP.Threefold.Bridges.exists_polynomial_inter_hyperplanes (k := ℂ)
    (fun _ : Unit => φ '' Sb) (fun _ => hcons (φ.isClosedEmbedding.isClosedMap _ hSbc))
    (d + 1)
  -- the general complete intersection
  obtain ⟨c, hcP, -, hcurve⟩ := exists_completeIntersection_curve hpoly d (U.ι ≫ sX) hdimU
    (U.ι ≫ φ) (by rw [Category.assoc, hφs]) sX φ hφs (Pa * Pb * Pc)
    (mul_ne_zero (mul_ne_zero hPa hPb) hPc)
  rw [map_mul, map_mul] at hcP
  have hca := left_ne_zero_of_mul (left_ne_zero_of_mul hcP)
  have hcb := right_ne_zero_of_mul (left_ne_zero_of_mul hcP)
  have hcc := right_ne_zero_of_mul hcP
  set IC : X.IdealSheafData := ⨆ j, MMP.Threefold.Bridges.hyperplaneSection φ (c j) with hIC
  set Hc : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N')) := ⋂ j,
    ((Stacks.ProjectiveSpace.hyperplane (MMP.Threefold.Bridges.linearForm (c j))).support :
      Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N'))) with hHc
  have hmemIC : ∀ x : X, x ∈ (IC.support : Set X) ↔ φ x ∈ Hc := by
    intro x
    rw [hIC, Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.coe_iInf, Set.mem_iInter,
      hHc, Set.mem_iInter]
    refine forall_congr' fun j => ?_
    rw [MMP.Threefold.Bridges.hyperplaneSection, Scheme.IdealSheafData.support_comap]
    rfl
  have hrange : topologicalKrullDim (Set.range φ) = ((d + 2 : ℕ) : WithBot ℕ∞) := by
    rw [← Set.image_univ, topologicalKrullDim_image_of_isEmbedding' φ.isClosedEmbedding.isEmbedding,
      (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, hdimX]
  obtain ⟨hHa, -⟩ := (hcuta c hca ()).2 (by rw [hrange]; exact_mod_cast (by omega : d + 1 ≤ d + 2))
  have hHb : φ '' Ssing ∩ Hc = ∅ := (hcutb c hcb ()).1 (by
    rw [topologicalKrullDim_image_of_isEmbedding' φ.isClosedEmbedding.isEmbedding]
    exact hSsingdim.trans_lt (by exact_mod_cast (by omega : d < d + 1)))
  have hHc0 : topologicalKrullDim ↥(φ '' Sb ∩ Hc) ≤ 0 := by
    have hdimb : topologicalKrullDim (φ '' Sb) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
      rw [topologicalKrullDim_image_of_isEmbedding' φ.isClosedEmbedding.isEmbedding]; exact hSbdim
    by_cases hc : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (φ '' Sb)
    · obtain ⟨-, hsum⟩ := (hcutc c hcc ()).2 hc
      exact withBot_le_zero_of_add_le (m := d + 1) (hsum.le.trans hdimb)
    · push Not at hc
      rw [(hcutc c hcc ()).1 hc]
      have h0 : topologicalKrullDim ↥(∅ : Set (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ N'))) = ⊥ := by
        rw [topologicalKrullDim, Order.krullDim_eq_bot_iff]
        exact ⟨fun T => T.isIrreducible.nonempty.some.2⟩
      rw [h0]
      exact bot_le
  -- the cut lies in `U` and is nonempty
  have hICU : Set.range IC.subschemeι ⊆ (U : Set X) := by
    rintro _ ⟨y, rfl⟩
    by_contra hy
    have hyS : IC.subschemeι y ∈ (IC.support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y, rfl⟩
    have : φ (IC.subschemeι y) ∈ φ '' Ssing ∩ Hc := ⟨⟨_, hy, rfl⟩, (hmemIC _).1 hyS⟩
    rw [hHb] at this
    exact this
  have hJ : (⨆ j, MMP.Threefold.Bridges.hyperplaneSection (U.ι ≫ φ) (c j)) = IC.comap U.ι :=
    iSup_hyperplaneSection_comp U.ι φ c
  have hne : ((⨆ j, MMP.Threefold.Bridges.hyperplaneSection (U.ι ≫ φ) (c j)).support :
      Set U.toScheme).Nonempty := by
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hHa
    have hxIC : x ∈ (IC.support : Set X) := (hmemIC x).2 hx
    have hxU : x ∈ (U : Set X) :=
      hICU (by rw [Scheme.IdealSheafData.range_subschemeι]; exact hxIC)
    refine ⟨⟨x, hxU⟩, ?_⟩
    rw [hJ, Scheme.IdealSheafData.support_comap]
    exact hxIC
  obtain ⟨C, ι, hι, hvarC, hsmC, hC1, hkerC, hdegC⟩ := hcurve hne
  haveI := hι
  haveI := hvarC
  haveI := hsmC
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_ker_eq_comap U IC hICU ι (hkerC.trans hJ)
  haveI : IsIntegral C := hvarC.toIsIntegral
  haveI : IsClosedImmersion (ι ≫ U.ι) := by rw [← he]; infer_instance
  haveI : IsProper (ι ≫ U.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  haveI : IsProper ((ι ≫ U.ι) ≫ sX) := inferInstance
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ U.ι ≫ sX)
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (ι ≫ U.ι ≫ sX)
  haveI : IsNoetherian C := {}
  have hCIC : ∀ y : C, U.ι (ι y) ∈ (IC.support : Set X) := fun y => by
    have h1 : U.ι (ι y) = IC.subschemeι (e.hom y) := by
      rw [← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply]
    rw [h1, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩
  -- `C` is not contained in the support of `B'`
  have hnotB : ∃ c₀ : C, U.ι (ι c₀) ∉ (B'.supp : Set X) := by
    by_contra hall
    push Not at hall
    have hmapsto : ∀ y : C, ((ι ≫ U.ι) ≫ φ) y ∈ φ '' Sb ∩ Hc := fun y =>
      ⟨⟨_, hall y, rfl⟩, (hmemIC _).1 (hCIC y)⟩
    have hind : Topology.IsInducing
        (fun y : C => (⟨((ι ≫ U.ι) ≫ φ) y, hmapsto y⟩ : ↥(φ '' Sb ∩ Hc))) :=
      ((ι ≫ U.ι) ≫ φ).isClosedEmbedding.isInducing.codRestrict hmapsto
    have h1 := hind.topologicalKrullDim_le.trans hHc0
    rw [hC1] at h1
    exact absurd h1 (by decide)
  -- the degrees
  set κ := degreeOn ℂ (U.ι ≫ sX) ι hC1.le
    (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sX) ((d + 2 : ℕ) : ℤ)) with hκ
  set δ := degreeOn ℂ sX (ι ≫ U.ι) hC1.le EX.divisorialSheaf with hδ
  have hGc : G.IsCartier := hEXc.neg
  have hGU : G.restrictOpen U = N • K.restrictOpen U + B'.restrictOpen U := by
    ext W
    change G (OpenWeilRestriction.primeDivisorMap U.ι W) =
      N • K (OpenWeilRestriction.primeDivisorMap U.ι W) + B' (OpenWeilRestriction.primeDivisorMap U.ι W)
    rw [hB'def, Finsupp.sub_apply, Finsupp.smul_apply]
    abel
  have hdegG : G.degreeOn ℂ sX (ι ≫ U.ι) hC1.le hGc =
      Divisor.degreeOn ℂ (U.ι ≫ sX) ι hC1.le (G.restrictOpen U) (hcU _) := by
    haveI := hGc.isInvertibleModule_divisorialSheaf
    haveI := (hcU (G.restrictOpen U)).isInvertibleModule_divisorialSheaf
    haveI := MMP.Mori.isInvertible_pullback_obj U.ι G.divisorialSheaf
    change degreeOn ℂ sX (ι ≫ U.ι) hC1.le G.divisorialSheaf =
      degreeOn ℂ (U.ι ≫ sX) ι hC1.le (Divisor.divisorialSheaf (G.restrictOpen U))
    rw [degreeOn_eq_of_iso ℂ (U.ι ≫ sX) ι hC1.le
      (Divisor.divisorialSheafRestrictOpenIso G U ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _),
      degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sX) sX U.ι ι rfl hC1.le]
  have hadd : Divisor.degreeOn ℂ (U.ι ≫ sX) ι hC1.le (G.restrictOpen U) (hcU _) =
      N * Divisor.degreeOn ℂ (U.ι ≫ sX) ι hC1.le (K.restrictOpen U) (hcU _) +
        Divisor.degreeOn ℂ (U.ι ≫ sX) ι hC1.le (B'.restrictOpen U) (hcU _) := by
    rw [Divisor.degreeOn_congr hGU _ (((hcU _).nsmul N).add (hcU _)),
      Divisor.degreeOn_add ℂ (U.ι ≫ sX) ι hC1.le _ _ ((hcU _).nsmul N) (hcU _),
      Divisor.degreeOn_nsmul']
  have hKU : Divisor.degreeOn ℂ (U.ι ≫ sX) ι hC1.le (K.restrictOpen U) (hcU _) = κ := by
    haveI := (hcU (K.restrictOpen U)).isInvertibleModule_divisorialSheaf
    let eK : Divisor.divisorialSheaf (K.restrictOpen U) ≅
        Scheme.Hom.relativeDifferentialForms (U.ι ≫ sX) ((d + 2 : ℕ) : ℤ) :=
      Divisor.divisorialSheafRestrictOpenIso K U ≪≫ hK.iso
    exact degreeOn_eq_of_iso ℂ (U.ι ≫ sX) ι hC1.le eK
  have hB'U : 0 ≤ Divisor.degreeOn ℂ (U.ι ≫ sX) ι hC1.le (B'.restrictOpen U) (hcU _) := by
    obtain ⟨c₀, hc₀⟩ := hnotB
    refine (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff (U.ι ≫ sX) ι hC1.le (B'.restrictOpen U) (hcU _)
      (Finsupp.le_def.2 fun W => Finsupp.le_def.1 hB'eff _) ⟨c₀, fun hmem => hc₀ ?_⟩).1
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
    exact DivisorWithCoeffs.mem_supp_iff.2 ⟨OpenWeilRestriction.primeDivisorMap U.ι E, hE,
      (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι E (ι c₀)).2 hxE⟩
  have hGδ : G.degreeOn ℂ sX (ι ≫ U.ι) hC1.le hGc = -δ := by
    have h0 := Divisor.degreeOn_add ℂ sX (ι ≫ U.ι) hC1.le EX (-EX) hEXc hEXc.neg
    rw [Divisor.degreeOn_congr (add_neg_cancel EX) _ Divisor.isCartier_zero,
      Divisor.degreeOn_zero'] at h0
    have : EX.degreeOn ℂ sX (ι ≫ U.ι) hC1.le hEXc = δ := rfl
    linarith
  have hδκ : δ ≤ (N : ℤ) * -κ := by
    have := hdegG
    rw [hGδ, hadd, hKU] at this
    linarith
  have hδpos : 0 < δ := by
    rw [hδ, degreeOn_eq_invertibleCurveDegree]
    exact invertibleCurveDegree_pos_of_isAmple_of_not_subsingleton_range ℂ ((ι ≫ U.ι) ≫ sX) hC1
      (ι ≫ U.ι) (not_subsingleton_range_of_topologicalKrullDim_eq_one (ι ≫ U.ι)
        (ι ≫ U.ι).isClosedEmbedding.injective hC1) _ hEXamp
  -- the genus
  have hgenus : 1 ≤ genus (ι ≫ U.ι ≫ sX) := by
    have hcomb := hdegC inferInstance
    haveI hCcurve' : AlgebraicGeometry.IsCurve ℂ (ι ≫ U.ι ≫ sX) :=
      { topologicalKrullDim_eq_one := hC1 }
    have hcot := MMP.invertibleCurveDegree_relativeDifferentials_eq_of_isAlgClosed (ι ≫ U.ι ≫ sX)
    have h2g : (2 * (genus (ι ≫ U.ι ≫ sX) : ℤ) - 2) = κ + ((d + 1 : ℕ) : ℤ) *
        degreeOn ℂ (U.ι ≫ sX) ι hC1.le ((Scheme.Modules.pullback (U.ι ≫ φ)).obj
          (MMP.Threefold.Bridges.twistOne ℂ N')) := by
      rw [genus_eq_finrank_structureSheafCohomology]
      exact hcot.symm.trans hcomb
    set lam := degreeOn ℂ (U.ι ≫ sX) ι hC1.le L₁ with hlam
    have hψ : degreeOn ℂ (U.ι ≫ sX) ι hC1.le ((Scheme.Modules.pullback (U.ι ≫ φ)).obj
        (MMP.Threefold.Bridges.twistOne ℂ N')) = (m : ℤ) * lam := by
      haveI := MMP.Mori.isInvertible_pullback_obj φ (MMP.Threefold.Bridges.twistOne ℂ N')
      have e₃ : (Scheme.Modules.pullback (U.ι ≫ φ)).obj
          (MMP.Threefold.Bridges.twistOne ℂ N') ≅ (Scheme.Modules.pullback U.ι).obj
            (Stacks.Ample.tensorPowModule X L (m : ℤ)) :=
        ((Scheme.Modules.pullbackComp U.ι φ).app _).symm ≪≫
          (Scheme.Modules.pullback U.ι).mapIso eφ.symm
      haveI := MMP.Mori.isInvertible_pullback_obj U.ι (Stacks.Ample.tensorPowModule X L (m : ℤ))
      rw [degreeOn_eq_of_iso ℂ (U.ι ≫ sX) ι hC1.le e₃,
        degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sX) sX U.ι ι rfl hC1.le,
        degreeOn_tensorPowModule_natCast', hlam,
        degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sX) sX U.ι ι rfl hC1.le]
    have hlampos : 0 < lam := by
      rw [hlam, degreeOn_eq_invertibleCurveDegree]
      exact invertibleCurveDegree_pos_of_isAmple_of_not_subsingleton_range ℂ (ι ≫ U.ι ≫ sX) hC1
        ι (not_subsingleton_range_of_topologicalKrullDim_eq_one ι ι.isClosedEmbedding.injective hC1)
        L₁ ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hL₁)
    have hn : -((n₁ : ℤ) * lam) ≤ κ := hn₁ ι hC1.le
    have hm1 : n₁ + 1 ≤ m := le_max_right _ _
    rw [hψ] at h2g
    have hm1' : ((n₁ : ℤ) + 1) ≤ ((d + 1 : ℕ) : ℤ) * (m : ℤ) := by
      have : ((n₁ : ℤ) + 1) ≤ (m : ℤ) := by exact_mod_cast hm1
      exact this.trans (le_mul_of_one_le_left (Int.natCast_nonneg m) (by omega))
    have hpos : (0 : ℤ) < 2 * (genus (ι ≫ U.ι ≫ sX) : ℤ) - 2 := by
      have h3 : ((n₁ : ℤ) + 1) * lam ≤ ((d + 1 : ℕ) : ℤ) * (m : ℤ) * lam :=
        mul_le_mul_of_nonneg_right hm1' hlampos.le
      rw [h2g]
      linarith only [h3, hn, hlampos]
    omega
  haveI hCcurve : AlgebraicGeometry.IsCurve ℂ (ι ≫ U.ι ≫ sX) := { topologicalKrullDim_eq_one := hC1 }
  have hCproj : AlgebraicGeometry.IsProjectiveVariety ℂ (ι ≫ U.ι ≫ sX) := by
    obtain ⟨N'', φ', hφ', hφs'⟩ := (‹AlgebraicGeometry.IsProjectiveVariety ℂ sX›).isProjective
    haveI := hφ'
    exact { isProjective := ⟨N'', (ι ≫ U.ι) ≫ φ', inferInstance, by
      simp only [Category.assoc, hφs']⟩ }
  refine ⟨hUsm, C, ι, hι, hCcurve, hCproj, hsmC, hgenus, ?_, ?_⟩
  · change κ < 0
    have : (0 : ℤ) < N := by exact_mod_cast hN
    exact neg_pos.mp (pos_of_mul_pos_right (hδpos.trans_le hδκ) this.le)
  · change (δ : ℚ) ≤ N * -(κ : ℚ)
    exact_mod_cast hδκ

/-- **The case `r = n ≥ 2`.** The fibre is all of `X`, so `-(K + B)` is ample on `X`, and the
slope bound on the smooth locus of `X` itself gives the rational curve. -/
private theorem exists_rationalCurve_of_eq {d : ℕ} {K : Divisor X} {B : QDivisor X}
    (hklt : IsKltPair sX (d + 2) K B) (hB : 0 ≤ B) {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    (hamp : MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor (-(Divisor.toQDivisor K + B))))
    (z : Z) (hfz : ∀ x : X, f x = z) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    ∃ T : ProperCurve sX,
      IsRationalCurve sX
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) ∧
        0 < -(Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 ∧
        -(Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 ≤
          2 * ((d + 2 : ℕ) : ℚ) := by
  haveI := hf.isNormalVariety_target.1
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hf.isNormalVariety_target.2
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  -- an `f`-ample Cartier divisor `E_X` with `E_X = N (-(K + B))`, ample on `X`
  obtain ⟨m, A, c, N, hm, hN, hc, hA, hE⟩ := exists_nat_presentation hamp
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  set EX := ∑ j, c j • A j with hEXdef
  have hEXc : EX.IsCartier := isCartier_sum_nsmul A hAc c Finset.univ
  have hEXamp : MMP.Flips.IsRelativelyAmpleCartier f EX := by
    refine (MMP.Flips.relativelyAmple_basics sX sZ hklt.1.1 hf.isNormalVariety_target f
      hf.comp_eq).2.2.2.2.1 EX hEXc ⟨m, fun j => (c j : ℝ), A, hm,
        fun j => by simp only; exact_mod_cast hc j, hA, ?_⟩
    simp only [hEXdef, map_sum, map_nsmul, Nat.cast_smul_eq_nsmul]
  have hE' : Divisor.toQDivisor EX = (N : ℤ) • -(Divisor.toQDivisor K + B) := hE
  haveI := hEXc.isInvertibleModule_divisorialSheaf
  have hMamp := isAmple_pullback_of_isRelativelyAmpleCartier hEXamp (𝟙 X) z hfz
  have hXamp : Scheme.Modules.IsAmple X EX.divisorialSheaf :=
    @Scheme.Modules.isAmple_of_iso X _ _
      (MMP.Mori.isInvertible_pullback_obj (𝟙 X) EX.divisorialSheaf) inferInstance
      ((Scheme.Modules.pullbackId X).app _) hMamp
  haveI := MMP.Mori.isInvertible_pullback_obj (𝟙 X) EX.divisorialSheaf
  -- the ample `ℚ`-divisor `H = -(K + B)`
  set H : QDivisor X := (N : ℚ)⁻¹ • Divisor.toQDivisor EX with hHdef
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hEXH : Divisor.toQDivisor EX = ((N : ℕ) : ℤ) • H := by
    rw [hHdef, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ hNq, one_smul]
  have hHq : H.IsQCartier := ⟨N, by exact_mod_cast hN.ne', ⟨EX, hEXH, hEXc⟩⟩
  have hHamp : H.IsAmple := by
    refine ⟨N, hN, EX, ?_, hEXc, ?_⟩
    · rw [hEXH, ← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl
    · exact (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp hXamp
  -- the curve and the slope bound
  obtain ⟨hU, C, j, hj, hCcurve, hCproj, hCsm, hg1, hκ, hbound⟩ :=
    exists_slope_curve_of_eq (fun U hU => MMP.Mori.exists_polynomial_dualPoint_mem U hU) hklt hB hN
      hEXc hE' hXamp
  haveI := hU
  obtain ⟨L, hL, hLpos, hLle⟩ :=
    MMP.Fourfold.exists_isRationalCurve_intersectionNumber_le sX (smoothLocus sX) (d + 2) j hg1
      hκ H hHq hHamp
  have hHW : ∀ {W : Scheme.{0}} (w : W ⟶ X) [IsProper (w ≫ sX)] (hdim : topologicalKrullDim W ≤ 1),
      H.intersectionNumber ℂ sX w hdim hHq =
        (degreeOn ℂ sX w hdim EX.divisorialSheaf : ℚ) / N := by
    intro W w _ hdim
    rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX w hdim H hHq hN EX hEXc hEXH]
    rfl
  rw [hHW] at hLpos hLle
  rw [hHW] at hLle
  haveI := hL.2.1
  have hId : ∀ {W : Scheme.{0}} (w : W ⟶ X) [IsProper (w ≫ sX)] (hdim : topologicalKrullDim W ≤ 1),
      degreeOn ℂ sX w hdim ((Scheme.Modules.pullback (𝟙 X)).obj EX.divisorialSheaf) =
        degreeOn ℂ sX w hdim EX.divisorialSheaf := fun w _ hdim =>
    degreeOn_eq_of_iso ℂ sX w hdim ((Scheme.Modules.pullbackId X).app _)
  have hpos : 0 < degreeOn ℂ sX L.subschemeι hL.1.2.le
      ((Scheme.Modules.pullback (𝟙 X)).obj EX.divisorialSheaf) := by
    rw [hId]
    have := div_pos_iff.mp hLpos
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (not_lt.mpr (by positivity))
  obtain ⟨T, hTrat, -, e, he, hdeg⟩ := exists_properCurve_image_of_isRationalCurve (k := ℂ)
    (sX := sX) (𝟙 X) (Category.id_comp _) L hL EX.divisorialSheaf hpos
  rw [hId] at hdeg
  refine ⟨T, hTrat, ?_⟩
  -- `-(K + B) · T = (H · L) / e`
  have hEneg : Divisor.toQDivisor (-EX) = ((N : ℕ) : ℤ) • (Divisor.toQDivisor K + B) := by
    rw [map_neg, hE', smul_neg, neg_neg]
  have hDT := QDivisor.intersectionNumber_eq_of_smul ℂ sX T.ι T.dim_le _ hklt.1.2.2 hN (-EX)
    hEXc.neg hEneg
  have h0 := Divisor.degreeOn_add ℂ sX T.ι T.dim_le EX (-EX) hEXc hEXc.neg
  rw [Divisor.degreeOn_congr (add_neg_cancel EX) _ Divisor.isCartier_zero,
    Divisor.degreeOn_zero'] at h0
  set dT := EX.degreeOn ℂ sX T.ι T.dim_le hEXc with hdT
  have hdT' : dT = degreeOn ℂ sX T.ι T.dim_le EX.divisorialSheaf := rfl
  have hval : -(Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 =
      (dT : ℚ) / N := by
    rw [hDT]
    have : ((-EX).degreeOn ℂ sX T.ι T.dim_le hEXc.neg : ℚ) = -dT := by
      have : (-EX).degreeOn ℂ sX T.ι T.dim_le hEXc.neg = -dT := by linarith
      exact_mod_cast this
    rw [this, neg_div, neg_neg]
  rw [hval]
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have hepos : (0 : ℚ) < e := by exact_mod_cast he
  rw [hdeg, ← hdT'] at hLpos hLle
  simp only [Int.cast_mul, Int.cast_natCast] at hLpos hLle
  have hdTpos : (0 : ℚ) < dT := by
    have := (div_pos_iff.mp hLpos)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact pos_of_mul_pos_right h1 hepos.le
    · exact absurd h2 (not_lt.mpr hNpos.le)
  refine ⟨div_pos hdTpos hNpos, ?_⟩
  have key : ∀ a b : ℚ, 0 < b → a ≤ N * b →
      2 * ((d + 2 : ℕ) : ℚ) * (a / N) / b ≤ 2 * ((d + 2 : ℕ) : ℚ) := by
    intro a b hb hab
    rw [div_le_iff₀ hb]
    have : a / N ≤ b := by rw [div_le_iff₀ hNpos]; linarith
    have h2 : (0 : ℚ) ≤ 2 * ((d + 2 : ℕ) : ℚ) := by positivity
    nlinarith
  have h1 := hLle.trans (key _ _ (by have := neg_pos.mpr hκ; exact_mod_cast this) hbound)
  have he1 : (1 : ℚ) ≤ e := by exact_mod_cast he
  have h2 : (dT : ℚ) / N ≤ e * dT / N := by
    rw [mul_div_assoc]
    exact le_mul_of_one_le_left (div_pos hdTpos hNpos).le he1
  push_cast at h1 ⊢
  linarith

/-- **The case `r ≥ 2`.** The slope bound on the normalization `V` of a maximal-dimensional
component of the fibre, applied to the ample `ℚ`-divisor `ν^*(-(K + B))`, gives a rational curve
on `V` whose image in `X` is the required curve. -/
private theorem exists_rationalCurve_of_two_le {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hklt : IsKltPair sX n K B) (hB : 0 ≤ B) {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    (hamp : MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor (-(Divisor.toQDivisor K + B))))
    (z : Z) (η : X) (hηF : closure ({η} : Set X) ⊆ f ⁻¹' {z})
    {r : ℕ} (hr2 : 2 ≤ r) (hrn : r + 1 ≤ n)
    (hdimE : topologicalKrullDim (curveSubschemeAt η) = r)
    (hfib : topologicalKrullDim (f ⁻¹' {z}) = r) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    ∃ T : ProperCurve sX,
      IsRationalCurve sX
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) ∧
        closure ({T.point} : Set X) ⊆ f ⁻¹' {z} ∧
        0 < -(Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 ∧
        -(Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 ≤ 2 * n := by
  haveI := hf.isNormalVariety_target.1
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hf.isNormalVariety_target.2
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  set D := Divisor.toQDivisor K + B with hD
  -- an `f`-ample Cartier divisor `E_X` with `E_X = N (-D)`
  obtain ⟨m, A, c, N, hm, hN, hc, hA, hE⟩ := exists_nat_presentation hamp
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  set EX := ∑ j, c j • A j with hEXdef
  have hEXc : EX.IsCartier := isCartier_sum_nsmul A hAc c Finset.univ
  have hEXamp : MMP.Flips.IsRelativelyAmpleCartier f EX := by
    refine (MMP.Flips.relativelyAmple_basics sX sZ hklt.1.1 hf.isNormalVariety_target f
      hf.comp_eq).2.2.2.2.1 EX hEXc ⟨m, fun j => (c j : ℝ), A, hm,
        fun j => by simp only; exact_mod_cast hc j, hA, ?_⟩
    simp only [hEXdef, map_sum, map_nsmul, Nat.cast_smul_eq_nsmul]
  have hE' : Divisor.toQDivisor EX = (N : ℤ) • -(Divisor.toQDivisor K + B) := hE
  -- the normalization `ν : V ⟶ E` of the component `E = {η}⁻`
  set i := curveSubschemeAtι η with hi
  haveI : IsIntegral (curveSubschemeAt η) :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure η
  haveI hEvar : AlgebraicGeometry.IsVariety ℂ (i ≫ sX) := { toIsIntegral := inferInstance }
  have hEproj : IsProjectiveMorphism (i ≫ sX) := by
    obtain ⟨N', φ, hφ, hφs⟩ := (‹AlgebraicGeometry.IsProjectiveVariety ℂ sX›).isProjective
    haveI := hφ
    exact ⟨N', i ≫ φ, inferInstance, by rw [Category.assoc, hφs]⟩
  set ν := normalizationOverField ℂ (i ≫ sX) with hν
  haveI : IsFinite ν := isFinite_normalizationOverField ℂ (i ≫ sX)
  haveI hVvar : AlgebraicGeometry.IsVariety ℂ (ν ≫ i ≫ sX) :=
    isVariety_normalizationOverField ℂ (i ≫ sX)
  haveI : IsProper (i ≫ sX) := isProper_of_isProjectiveMorphism _ hEproj
  haveI hVproj : AlgebraicGeometry.IsProjectiveVariety ℂ (ν ≫ i ≫ sX) :=
    { isProjective := (isProjective_iff_isProjectiveMorphism_of_isAffine _).mp
        ((isProper_and_isProjective_normalizationOverField ℂ (i ≫ sX)).2
          ((isProjective_iff_isProjectiveMorphism_of_isAffine _).mpr hEproj)) }
  haveI : IsNormal (normalizationSchemeOverField ℂ (i ≫ sX)) :=
    Scheme.isNormal_normalizationScheme _ _
  haveI : IsLocallyNoetherian (normalizationSchemeOverField ℂ (i ≫ sX)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ν ≫ i ≫ sX)
  haveI : CompactSpace (normalizationSchemeOverField ℂ (i ≫ sX)) :=
    QuasiCompact.compactSpace_of_compactSpace (ν ≫ i ≫ sX)
  haveI : IsIntegral (normalizationSchemeOverField ℂ (i ≫ sX)) := hVvar.toIsIntegral
  set g := ν ≫ i with hgdef
  haveI : IsFinite g := by rw [hgdef]; infer_instance
  haveI := hEXc.isInvertibleModule_divisorialSheaf
  have hgz : ∀ v, f (g v) = z := fun v => by
    have : i (ν v) ∈ closure ({η} : Set X) := by
      rw [← range_curveSubschemeAtι η]; exact ⟨_, rfl⟩
    exact hηF this
  have hMamp := isAmple_pullback_of_isRelativelyAmpleCartier hEXamp g z hgz
  -- the ample `ℚ`-divisor `H = ν^*(-(K + B))` on `V`
  obtain ⟨Δ, hΔc, ⟨eΔ⟩⟩ := exists_isCartier_divisorialSheaf_iso_pullback g hEXc
  haveI := hΔc.isInvertibleModule_divisorialSheaf
  set H : QDivisor (normalizationSchemeOverField ℂ (i ≫ sX)) :=
    (N : ℚ)⁻¹ • Divisor.toQDivisor Δ with hHdef
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hΔH : Divisor.toQDivisor Δ = ((N : ℕ) : ℤ) • H := by
    rw [hHdef, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ hNq, one_smul]
  have hHq : H.IsQCartier := ⟨N, by exact_mod_cast hN.ne', ⟨Δ, hΔH, hΔc⟩⟩
  have hHamp : H.IsAmple := by
    refine ⟨N, hN, Δ, ?_, hΔc, ?_⟩
    · rw [hΔH, ← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl
    · have := MMP.Mori.isInvertible_pullback_obj g EX.divisorialSheaf
      exact (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp
        (Scheme.Modules.isAmple_of_iso eΔ.symm hMamp)
  -- the curve and the slope bound
  obtain ⟨U, hU, C, j, hj, hCcurve, hCproj, hCsm, hg1, hκ, hbound⟩ :=
    exists_slope_curve_of_lt (fun U hU => MMP.Mori.exists_polynomial_dualPoint_mem U hU) hklt hB
      hf z η hηF hr2 hrn hdimE hfib hN hEXc hE' hEXamp
  obtain ⟨L, hL, hLpos, hLle⟩ :=
    MMP.Fourfold.exists_isRationalCurve_intersectionNumber_le (ν ≫ i ≫ sX) U r j hg1 hκ H hHq
      hHamp
  -- `H · W = (1/N) deg_W g^* 𝒪(E_X)`
  have hHW : ∀ {W : Scheme.{0}} (w : W ⟶ normalizationSchemeOverField ℂ (i ≫ sX))
      [IsProper (w ≫ ν ≫ i ≫ sX)] (hdim : topologicalKrullDim W ≤ 1),
      H.intersectionNumber ℂ (ν ≫ i ≫ sX) w hdim hHq =
        (degreeOn ℂ (ν ≫ i ≫ sX) w hdim ((Scheme.Modules.pullback g).obj EX.divisorialSheaf) : ℚ)
          / N := by
    intro W w _ hdim
    rw [QDivisor.intersectionNumber_eq_of_smul ℂ (ν ≫ i ≫ sX) w hdim H hHq hN Δ hΔc hΔH]
    congr 2
    exact degreeOn_eq_of_iso ℂ (ν ≫ i ≫ sX) w hdim eΔ
  rw [hHW] at hLpos hLle
  rw [hHW] at hLle
  -- the image of `L` in `X`
  haveI := hL.2.1
  have hpos : 0 < degreeOn ℂ (ν ≫ i ≫ sX) L.subschemeι hL.1.2.le
      ((Scheme.Modules.pullback g).obj EX.divisorialSheaf) := by
    have := div_pos_iff.mp hLpos
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (not_lt.mpr (by positivity))
  obtain ⟨T, hTrat, hTsub, e, he, hdeg⟩ := exists_properCurve_image_of_isRationalCurve (k := ℂ)
    (sX := sX) g (by rw [hgdef, Category.assoc]) L hL EX.divisorialSheaf hpos
  refine ⟨T, hTrat, ?_, ?_⟩
  · refine hTsub.trans (Set.Subset.trans ?_ hηF)
    rintro _ ⟨v, rfl⟩
    rw [← range_curveSubschemeAtι η]
    exact ⟨ν v, rfl⟩
  -- `-(K + B) · T = (H · L) / e`
  have hEneg : Divisor.toQDivisor (-EX) = ((N : ℕ) : ℤ) • (Divisor.toQDivisor K + B) := by
    rw [map_neg, hE', smul_neg, neg_neg]
  have hDT := QDivisor.intersectionNumber_eq_of_smul ℂ sX T.ι T.dim_le _ hklt.1.2.2 hN (-EX)
    hEXc.neg hEneg
  have h0 := Divisor.degreeOn_add ℂ sX T.ι T.dim_le EX (-EX) hEXc hEXc.neg
  rw [Divisor.degreeOn_congr (add_neg_cancel EX) _ Divisor.isCartier_zero,
    Divisor.degreeOn_zero'] at h0
  set dT := EX.degreeOn ℂ sX T.ι T.dim_le hEXc with hdT
  have hdT' : dT = degreeOn ℂ sX T.ι T.dim_le EX.divisorialSheaf := rfl
  have hval : -(Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 =
      (dT : ℚ) / N := by
    rw [hDT]
    have : ((-EX).degreeOn ℂ sX T.ι T.dim_le hEXc.neg : ℚ) = -dT := by
      have : (-EX).degreeOn ℂ sX T.ι T.dim_le hEXc.neg = -dT := by linarith
      exact_mod_cast this
    rw [this, neg_div, neg_neg]
  rw [hval]
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have hepos : (0 : ℚ) < e := by exact_mod_cast he
  rw [hdeg, ← hdT'] at hLpos hLle
  push_cast at hLpos hLle
  have hdTpos : (0 : ℚ) < dT := by
    have := (div_pos_iff.mp hLpos)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact pos_of_mul_pos_right h1 hepos.le
    · exact absurd h2 (not_lt.mpr hNpos.le)
  refine ⟨div_pos hdTpos hNpos, ?_⟩
  have key : ∀ a b : ℚ, 0 < b → a ≤ N * b → 2 * (r : ℚ) * (a / N) / b ≤ 2 * r := by
    intro a b hb hab
    rw [div_le_iff₀ hb]
    have : a / N ≤ b := by rw [div_le_iff₀ hNpos]; linarith
    nlinarith
  have h1 := hLle.trans (key _ _ (by have := neg_pos.mpr hκ; exact_mod_cast this) hbound)
  have he1 : (1 : ℚ) ≤ e := by exact_mod_cast he
  have hrn' : (r : ℚ) ≤ n := by exact_mod_cast (by omega : r ≤ n)
  have h2 : (dT : ℚ) / N ≤ e * dT / N := by
    rw [mul_div_assoc]
    exact le_mul_of_one_le_left (div_pos hdTpos hNpos).le he1
  linarith

/-- The core: a positive-dimensional closed fibre contains a rational curve of bounded
anti-canonical degree. -/
private theorem exists_rationalCurve_in_fibre {n : ℕ} (hn : 1 ≤ n) {K : Divisor X}
    {B : QDivisor X} (hklt : IsKltPair sX n K B) (hB : 0 ≤ B)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    (hamp : MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor (-(Divisor.toQDivisor K + B))))
    (z : Z) (hz : IsClosed ({z} : Set Z)) (hdim : 0 < topologicalKrullDim (f ⁻¹' {z})) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian sX
    ∃ T : ProperCurve sX,
      IsRationalCurve sX
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) ∧
        closure ({T.point} : Set X) ⊆ f ⁻¹' {z} ∧
        0 < -(Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 ∧
        -(Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 ≤ 2 * n := by
  set F := f ⁻¹' {z} with hFdef
  have hFc : IsClosed F := hz.preimage f.continuous
  have hFne : F.Nonempty := by
    obtain ⟨x, hx⟩ := hf.surjective z
    exact ⟨x, hx⟩
  haveI : IsNoetherian X := {}
  obtain ⟨η, hηF, hdimη⟩ := exists_closure_singleton_subset_topologicalKrullDim_eq hFc hFne
  have hFn : topologicalKrullDim F ≤ n :=
    (topologicalKrullDim_subspace_le X F).trans_eq hklt.1.2.1.1
  obtain ⟨r, hr⟩ : ∃ r : ℕ, topologicalKrullDim F = r := by
    generalize topologicalKrullDim F = d at hFn hdim
    cases d using WithBot.recBotCoe with
    | bot => exact absurd hdim (not_lt_bot)
    | coe e =>
      cases e using ENat.recTopCoe with
      | top => exact absurd hFn (by norm_cast)
      | coe r => exact ⟨r, rfl⟩
  have hr1 : 1 ≤ r := by
    rw [hr] at hdim
    exact_mod_cast Order.one_le_iff_pos.mpr (by exact_mod_cast hdim)
  have hrn : r ≤ n := by
    rw [hr] at hFn; exact_mod_cast hFn
  have hdimE : topologicalKrullDim (curveSubschemeAt η) = r := by
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hdimη, hr]
  have hneg : ∀ C : ProperCurve sX, closure ({C.point} : Set X) ⊆ F →
      (Divisor.toQDivisor K + B).intersectionNumber ℂ sX C.ι C.dim_le hklt.1.2.2 < 0 :=
    fun C hC => intersectionNumber_neg_of_isRelativelyAmple hklt.1.2.2 hamp C fun x hx => by
      rw [hC hx, hC (subset_closure rfl)]
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · obtain rfl : r = 1 := by omega
    let T : ProperCurve sX := ⟨η, isProperCurve_of_isProper sX (by exact_mod_cast hdimE)⟩
    obtain ⟨hrat, hle⟩ := isRationalCurve_and_neg_intersectionNumber_le_two hklt hB hf z hz
      (by rw [hr]; exact le_rfl) T hηF (hneg T hηF)
    refine ⟨T, hrat, hηF, by linarith [hneg T hηF], hle.trans ?_⟩
    exact_mod_cast (by omega : 2 ≤ 2 * n)
  · rcases Nat.lt_or_ge r n with hrn' | hrn'
    · exact exists_rationalCurve_of_two_le hklt hB hf hamp z η hηF hr2 hrn' hdimE hr
    · obtain rfl : r = n := le_antisymm hrn hrn'
      obtain ⟨d, rfl⟩ : ∃ d, r = d + 2 := ⟨r - 2, by omega⟩
      have hFu : F = Set.univ := by
        by_contra hne
        have h1 := Topology.topologicalKrullDim_add_one_le_of_ne_univ hFc hne
        rw [hr, hklt.1.2.1.1] at h1
        have h2 : (((d + 2 : ℕ) + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + 2 : ℕ) : WithBot ℕ∞) := by
          push_cast at h1 ⊢; exact h1
        have h3 : d + 2 + 1 ≤ d + 2 := by exact_mod_cast h2
        omega
      have hfz : ∀ x : X, f x = z := fun x => by
        have : x ∈ F := hFu ▸ Set.mem_univ x
        exact this
      obtain ⟨T, hTrat, hpos, hle⟩ := exists_rationalCurve_of_eq hklt hB hf hamp z hfz
      exact ⟨T, hTrat, fun x _ => hfz x, hpos, hle⟩

end Main

end MMP.FourfoldProofs.FourfoldProjectiveComplexKltContractionLengthProof

end

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

namespace MMP.Fourfold

open MMP.FourfoldProofs.FourfoldProjectiveComplexKltContractionLengthProof in
/-- **Bounded rational curves in the fibres of a klt contraction.** Let `(X, B)` be a klt pair,
with `B ≥ 0` a `ℚ`-divisor, `K` a canonical divisor of dimension `n ≥ 1` and `X` a projective
complex variety, and let `f : X ⟶ Z` be a contraction which is not an isomorphism, with
`-(K + B)` ample over `Z`. Then some fibre of `f` over a closed point has positive dimension, and
every such fibre `f⁻¹(z)` contains a rational curve `T` with `0 < -(K + B) · T ≤ 2n`; if `f` is
the contraction of an extremal ray `R` of `NE̅(X)`, then `R = ℝ_{≥0} · [T]`. -/
@[mmp "lem_fourfold_projective_complex_klt_contraction_length"]
public theorem exists_isRationalCurve_of_isContraction_of_isRelativelyAmple_neg
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsProjectiveVariety ℂ sX] [CompactSpace X]
    {n : ℕ} (hn : 1 ≤ n) {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B)
    (hB : 0 ≤ B)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (hf : IsContraction sX sZ f)
    (hnt : ¬ IsIso f)
    (hamp : MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor (-(Divisor.toQDivisor K + B)))) :
    (∃ z : Z, IsClosed ({z} : Set Z) ∧ 0 < topologicalKrullDim (f ⁻¹' {z})) ∧
      ∀ z : Z, IsClosed ({z} : Set Z) → 0 < topologicalKrullDim (f ⁻¹' {z}) →
        ∃ T : ProperCurve sX,
          IsRationalCurve sX
              (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) ∧
            closure ({T.point} : Set X) ⊆ f ⁻¹' {z} ∧
            0 < -QDivisor.curveForm sX (Divisor.toQDivisor K + B) hklt.1.2.2
                (OneCycle.numericalClass sX (T.cycle ℝ)) ∧
            -QDivisor.curveForm sX (Divisor.toQDivisor K + B) hklt.1.2.2
                (OneCycle.numericalClass sX (T.cycle ℝ)) ≤ 2 * n ∧
            ∀ R : Set (NumericalCurveClasses sX),
              IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R →
              IsContractionOfRay sX sZ R f →
                R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (T.cycle ℝ) = w} := by
  refine ⟨exists_isClosed_topologicalKrullDim_fibre_pos hf hnt, fun z hz hdim => ?_⟩
  obtain ⟨T, hTrat, hTz, hpos, hle⟩ := exists_rationalCurve_in_fibre hn hklt hB hf hamp z hz hdim
  have hform := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX
    (Divisor.toQDivisor K + B) hklt.1.2.2 T
  refine ⟨T, hTrat, hTz, ?_, ?_, fun R hR hRf => eq_ray_of_mem hR ?_ ?_⟩
  · rw [hform]; exact_mod_cast hpos
  · rw [hform]; exact_mod_cast hle
  · refine (hRf.isContractedBy_iff T).1 fun x hx => ?_
    rw [hTz hx, hTz (subset_closure rfl)]
  · intro h0
    rw [h0, map_zero] at hform
    have : ((Divisor.toQDivisor K + B).intersectionNumber ℂ sX T.ι T.dim_le hklt.1.2.2 : ℝ) = 0 :=
      hform.symm
    exact hpos.ne' (by rw [neg_eq_zero]; exact_mod_cast this)

end MMP.Fourfold

end
