module

public import MMP.AlgebraicGeometry.ChowForm.AvoidingPair

/-!
# Restriction of the Koszul family to a fibre

Auxiliary declarations for the Chow form of a proper flat family of curves
(`MMP.Chow.DeterminantCurveForm`), split out of the proof of the determinant curve form.

## References

* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3
-/

@[expose] public section

universe u v w

namespace MMP.Chow.DeterminantCurveForm

open MMP CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ProjPolyChart MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Defs

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{u}} {N : ℕ}

section CoreLemmas

attribute [local instance] LocalFreeData.isOpenImmersion LocalFreeData.isAffine
  LocalFreeData.isDomain LocalFreeData.isNoetherian LocalFreeData.isIntegrallyClosed
  LocalFreeData.locFT

attribute [local instance] KoszulFamily.invertible

variable {g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)} {S 𝒞 : Scheme.{u}}
  {sS : S ⟶ Spec (.of k)} {π : 𝒞 ⟶ S} {q : 𝒞 ⟶ Y} {d : ℕ} {s : S}

section FibreChow

attribute [local instance] isInvertibleModule_fibreH
attribute [local instance] isNoetherian_proj

section FibreRestrict

open Opposite

/-- **Proportional morphisms have proportional pulled back stalk maps.** -/
theorem stalkLinearMap_pullback_map_eq_smul {X Y : Scheme.{u}} (ρ : X ⟶ Y)
    {M N : Y.Modules} (f f' : M ⟶ N) (x : X) (r : Y.presheaf.stalk (ρ x))
    (h : stalkLinearMap M N f (ρ x) = r • stalkLinearMap M N f' (ρ x)) :
    stalkLinearMap _ _ ((Scheme.Modules.pullback ρ).map f) x =
      (ρ.stalkMap x).hom r • stalkLinearMap _ _ ((Scheme.Modules.pullback ρ).map f') x := by
  letI : Algebra (Y.presheaf.stalk (ρ x)) (X.presheaf.stalk x) := (ρ.stalkMap x).hom.toAlgebra
  have hAb : stalkLinearMapAb f (ρ x) = r • stalkLinearMapAb f' (ρ x) := by
    ext z; exact LinearMap.congr_fun h z
  ext z
  apply (Scheme.Modules.pullbackStalkEquiv ρ N x).injective
  rw [pullbackStalkEquiv_stalkLinearMap, hAb, LinearMap.smul_apply]
  erw [LinearEquiv.map_smul]
  rw [pullbackStalkEquiv_stalkLinearMap, LinearMap.baseChange_smul, LinearMap.smul_apply]
  exact (algebraMap_smul (X.presheaf.stalk x) r _).symm

/-- **Multiplication by proportional sections.** At a point where `τ` does not vanish, the stalk
map of multiplication by `σ` on the twists is the coordinate of `σ` in the basis `τ` times that of
multiplication by `τ`. -/
theorem stalkLinearMap_coordMul_eq_coord_smul {X : Scheme.{u}} (H A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X H] [Stacks.Ample.IsInvertibleModule X A] (n : ℕ) (m : ℤ)
    (σ τ : Γ(H, ⊤)) {y : X} (hτ : y ∈ Stacks.Ample.nonvanishingLocus H τ) :
    stalkLinearMap _ _ (MMP.Chow.coordMul H A σ n m) y =
      (Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus H τ hτ).coord
        ((H.presheaf.Γgerm y).hom σ) • stalkLinearMap _ _ (MMP.Chow.coordMul H A τ n m) y := by
  obtain ⟨F, -, hF⟩ := stalk_coordMul H A n m y
  set hb := Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus H τ hτ
  have hs : stalkLinearMap _ _ (Stacks.EnriquesSeveriZariski.sectionHom H σ) y =
      hb.coord ((H.presheaf.Γgerm y).hom σ) •
        stalkLinearMap _ _ (Stacks.EnriquesSeveriZariski.sectionHom H τ) y := by
    ext z
    rw [LinearMap.smul_apply, Stacks.EnriquesSeveriZariski.stalkLinearMap_sectionHom,
      Stacks.EnriquesSeveriZariski.stalkLinearMap_sectionHom]
    conv_lhs => rw [← hb.smul_coord ((H.presheaf.Γgerm y).hom σ)]
    exact smul_comm _ _ _
  rw [hF σ, hF τ, hs, map_smul]

/-- The germ of the pullback of a global section is the pullback of its germ. -/
theorem Γgerm_pullbackGlobalSections {X Y : Scheme.{u}} (ρ : X ⟶ Y) (L : Y.Modules)
    (σ : Γ(L, ⊤)) (x : X) :
    (((Scheme.Modules.pullback ρ).obj L).presheaf.Γgerm x).hom (pullbackGlobalSections ρ L σ) =
      Stacks.Divisors.pullbackStalk ρ L x ((L.presheaf.Γgerm (ρ x)).hom σ) := by
  refine Eq.trans ?_ (Stacks.Divisors.pullbackStalk_germ ρ L x ⊤ trivial σ).symm
  show (((Scheme.Modules.pullback ρ).obj L).presheaf.germ ⊤ x trivial).hom
      (((Scheme.Modules.pullback ρ).obj L).presheaf.map
        (eqToHom (show (⊤ : X.Opens) = ρ ⁻¹ᵁ ⊤ from rfl)).op
        (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections ρ L ⊤ σ)) = _
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- **Coordinates pull back.** The coordinate of the pullback of `σ` in the basis given by the
pullback of `τ` is the image of the coordinate of `σ` in the basis `τ`. -/
theorem coord_pullbackGlobalSections {X Y : Scheme.{u}} (ρ : X ⟶ Y) (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] [Stacks.Ample.IsInvertibleModule X
      ((Scheme.Modules.pullback ρ).obj L)] (σ τ : Γ(L, ⊤)) {x : X}
    (hτ : ρ x ∈ Stacks.Ample.nonvanishingLocus L τ)
    (hτ' : x ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback ρ).obj L)
      (pullbackGlobalSections ρ L τ)) :
    (Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus _ _ hτ').coord
        ((((Scheme.Modules.pullback ρ).obj L).presheaf.Γgerm x).hom
          (pullbackGlobalSections ρ L σ)) =
      (ρ.stalkMap x).hom
        ((Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus L τ hτ).coord
          ((L.presheaf.Γgerm (ρ x)).hom σ)) := by
  set hb := Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus L τ hτ
  set hb' := Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus _ _ hτ'
  have h : (((Scheme.Modules.pullback ρ).obj L).presheaf.Γgerm x).hom
      (pullbackGlobalSections ρ L σ) =
        (ρ.stalkMap x).hom (hb.coord ((L.presheaf.Γgerm (ρ x)).hom σ)) •
        (((Scheme.Modules.pullback ρ).obj L).presheaf.Γgerm x).hom
          (pullbackGlobalSections ρ L τ) := by
    rw [Γgerm_pullbackGlobalSections, Γgerm_pullbackGlobalSections,
      ← Stacks.Divisors.pullbackStalk_smul, hb.smul_coord]
  rw [h, hb'.coord_smul]

open Polynomial in
/-- The determinant of `c • 1 + φ`, for a nilpotent endomorphism `φ` of a finite-dimensional
space, is `c` to the power of the dimension. -/
theorem det_smul_one_add_of_isNilpotent {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (φ : Module.End K M) (hφ : IsNilpotent φ) (c : K) :
    LinearMap.det (c • (1 : Module.End K M) + φ) = c ^ Module.finrank K M := by
  have h2 := LinearMap.eval_charpoly φ (-c)
  rw [hφ.charpoly_eq_X_pow_finrank] at h2
  simp only [Polynomial.eval_pow, Polynomial.eval_X, map_neg] at h2
  have : -(algebraMap K (Module.End K M)) c - φ = (-1 : K) • (c • 1 + φ) := by
    rw [Algebra.algebraMap_eq_smul_one, neg_one_smul]
    abel
  rw [this, LinearMap.det_smul, neg_pow] at h2
  have h3 : ((-1 : K) ^ Module.finrank K M) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_left_cancel₀ h3 h2).symm

section LocalLength

variable {K R M : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
  [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]

/-- the residue field of `R` is spanned by `K` -/
def ResidueIsBase (K R : Type*) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R] : Prop :=
  ∀ r : R, ∃ c : K, r - algebraMap K R c ∈ IsLocalRing.maximalIdeal R

/-- If the residue field of `R` is spanned by `K`, the length of an `R`-module over `K` equals
its length over `R`. -/
theorem length_eq_length_of_residueIsBase (h : ResidueIsBase K R) :
    Module.length K M = Module.length R M := by
  haveI : IsLocalHom (algebraMap K R) :=
    ⟨fun a ha => by
      rcases eq_or_ne a 0 with rfl | h
      · rw [map_zero] at ha
        exact absurd ha not_isUnit_zero
      · exact isUnit_iff_ne_zero.2 h⟩
  have h1 : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField R) = 1 := by
    have hs : Function.Surjective
        (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField R)) := by
      intro z
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨c, hc⟩ := h r
      refine ⟨IsLocalRing.residue K c, ?_⟩
      rwa [IsLocalRing.ResidueField.algebraMap_residue, eq_comm, ← sub_eq_zero, ← map_sub,
        IsLocalRing.residue_eq_zero_iff]
    rw [Module.length_eq_of_surjective hs]
    exact Module.length_eq_one _ _
  rw [IsLocalRing.length_restrictScalars K R M, h1, mul_one]

/-- If the residue field of `R` is spanned by `K`, an `R`-module of finite length is
finite-dimensional over `K`. -/
theorem finiteDimensional_of_residueIsBase (h : ResidueIsBase K R) [IsArtinian R M]
    [IsNoetherian R M] : FiniteDimensional K M := by
  have hR : Module.length R M ≠ ⊤ :=
    Module.length_ne_top_iff.2 (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨‹_›, ‹_›⟩)
  rw [← length_eq_length_of_residueIsBase h] at hR
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 hR)).1
  exact Module.IsNoetherian.finite K M

/-- If the residue field of `R` is spanned by `K`, the dimension over `K` of an `R`-module of
finite length is its length over `R`. -/
theorem finrank_eq_length_of_residueIsBase (h : ResidueIsBase K R) [IsArtinian R M]
    [IsNoetherian R M] : (Module.finrank K M : ℕ∞) = Module.length R M := by
  haveI := finiteDimensional_of_residueIsBase (M := M) h
  rw [← length_eq_length_of_residueIsBase h, Module.length_eq_finrank]

/-- If the residue field of `R` is spanned by `K`, the dimension over `K` of an `R`-module of
finite length is the natural number its length over `R`. -/
theorem finrank_eq_length_toNat_of_residueIsBase (h : ResidueIsBase K R) [IsArtinian R M]
    [IsNoetherian R M] : Module.finrank K M = (Module.length R M).toNat := by
  rw [← finrank_eq_length_of_residueIsBase h, ENat.toNat_coe]

/-- **The determinant of a multiplication on a module of finite length** over a local ring with
residue field spanned by `K`: it is the power, by the dimension, of the residue of the
multiplier. -/
theorem det_lsmul_eq_pow_of_residueIsBase (h : ResidueIsBase K R) [IsArtinian R M]
    [IsNoetherian R M] {r : R} {c : K} (hc : r - algebraMap K R c ∈ IsLocalRing.maximalIdeal R) :
    LinearMap.det ((LinearMap.lsmul R M r).restrictScalars K) = c ^ Module.finrank K M := by
  haveI := finiteDimensional_of_residueIsBase (M := M) h
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isArtinian (M := M) _ hc
  have e : (LinearMap.lsmul R M r).restrictScalars K =
      c • (1 : Module.End K M) +
        (LinearMap.lsmul R M (r - algebraMap K R c)).restrictScalars K := by
    ext m
    simp [sub_smul, algebraMap_smul]
  rw [e, det_smul_one_add_of_isNilpotent]
  refine ⟨n, LinearMap.ext fun m => ?_⟩
  have hp : ∀ j : ℕ, ((LinearMap.lsmul R M (r - algebraMap K R c)).restrictScalars K) ^ j =
      (LinearMap.lsmul R M ((r - algebraMap K R c) ^ j)).restrictScalars K := by
    intro j
    induction j with
    | zero => ext; simp
    | succ j ih =>
      rw [pow_succ, ih]
      ext x
      simp only [Module.End.mul_apply, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply,
        pow_succ, mul_smul]
  rw [hp]
  simpa using hn m

end LocalLength

section BB

open Matrix

section KoszulReduction

variable {T : Type*} [CommRing T] {ι₂ ι₁ ι₀ δ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
  [Fintype δ] [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀] [DecidableEq δ]

/-- The comparison matrix `[L'a | J₀]⁻¹ [L'a | L'v J₁]`, indexed by `ι₀`. -/
noncomputable def koszulQ (σ : ι₀ ≃ ι₁ ⊕ δ) (L'a L'v : Matrix ι₀ ι₁ T) (J₁ : Matrix ι₁ δ T)
    (J₀ : Matrix ι₀ δ T) : Matrix ι₀ ι₀ T :=
  ((fromCols L'a J₀).submatrix id σ)⁻¹ * (fromCols L'a (L'v * J₁)).submatrix id σ

/-- The block of `koszulQ` from the `δ`-coordinates to the `δ`-coordinates: the matrix of the
map induced by `L'v` between the complements. -/
noncomputable def koszulY (σ : ι₀ ≃ ι₁ ⊕ δ) (L'a L'v : Matrix ι₀ ι₁ T) (J₁ : Matrix ι₁ δ T)
    (J₀ : Matrix ι₀ δ T) : Matrix δ δ T :=
  of fun i j => koszulQ σ L'a L'v J₁ J₀ (σ.symm (Sum.inr i)) (σ.symm (Sum.inr j))

/-- If `[L'a | J₀]` is invertible, the determinant of `[L'a | L'v J₁]` is the determinant of
`[L'a | J₀]` times the determinant of `koszulY`. -/
theorem det_fromCols_mul_eq (σ : ι₀ ≃ ι₁ ⊕ δ) (L'a L'v : Matrix ι₀ ι₁ T) (J₁ : Matrix ι₁ δ T)
    (J₀ : Matrix ι₀ δ T) (h0 : IsUnit ((fromCols L'a J₀).submatrix id σ).det) :
    ((fromCols L'a (L'v * J₁)).submatrix id σ).det =
      ((fromCols L'a J₀).submatrix id σ).det * (koszulY σ L'a L'v J₁ J₀).det := by
  set N := (fromCols L'a J₀).submatrix id σ
  set M := (fromCols L'a (L'v * J₁)).submatrix id σ
  set Q := koszulQ σ L'a L'v J₁ J₀
  have hNQ : N * Q = M := by
    show N * (N⁻¹ * M) = M
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h0, Matrix.one_mul]
  have hcol : ∀ a j, Q a (σ.symm (Sum.inl j)) = (1 : Matrix ι₀ ι₀ T) a (σ.symm (Sum.inl j)) := by
    intro a j
    have hMN : ∀ c, M c (σ.symm (Sum.inl j)) = N c (σ.symm (Sum.inl j)) := fun c => by
      simp [M, N]
    show (N⁻¹ * M) a _ = _
    rw [← Matrix.nonsing_inv_mul _ h0, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [hMN]
  have hQ1 : ∀ i j, Q (σ.symm (Sum.inl i)) (σ.symm (Sum.inl j)) = if i = j then 1 else 0 := by
    intro i j
    rw [hcol, Matrix.one_apply]
    simp
  have hQ0 : ∀ i j, Q (σ.symm (Sum.inr i)) (σ.symm (Sum.inl j)) = 0 := by
    intro i j
    rw [hcol, Matrix.one_apply]
    simp
  have hblk : Q.submatrix σ.symm σ.symm =
      fromBlocks 1 (of fun i j => Q (σ.symm (Sum.inl i)) (σ.symm (Sum.inr j))) 0
        (koszulY σ L'a L'v J₁ J₀) := by
    ext (i | i) (j | j)
    · simp [hQ1, Matrix.one_apply]
    · rfl
    · simp [hQ0]
    · rfl
  rw [← hNQ, Matrix.det_mul]
  congr 1
  rw [← Matrix.det_submatrix_equiv_self σ.symm Q, hblk, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul]

/-- The section `C = [1 0; 0 J₁]` used to compute the determinant of the Koszul complex at a fixed
first hyperplane. -/
noncomputable def koszulC (σ : ι₀ ≃ ι₁ ⊕ δ) (J₁ : Matrix ι₁ δ T) : Matrix (ι₁ ⊕ ι₁) ι₀ T :=
  (fromBlocks (1 : Matrix ι₁ ι₁ T) 0 0 J₁).submatrix id σ

/-- The product `[L'a | L'v] * koszulC σ J₁` is the matrix `[L'a | L'v J₁]`, with columns
reindexed along `σ`. -/
theorem fromCols_mul_koszulC (σ : ι₀ ≃ ι₁ ⊕ δ) (L'a L'v : Matrix ι₀ ι₁ T) (J₁ : Matrix ι₁ δ T) :
    fromCols L'a L'v * koszulC σ J₁ = (fromCols L'a (L'v * J₁)).submatrix id σ := by
  ext i j
  rcases h : σ j with a | a <;>
    simp [koszulC, Matrix.mul_apply, Fintype.sum_sum_type, h, Matrix.one_apply]

/-- If `[La | J₁]` is invertible, the square matrix `MMP.Chow.splitMatrix` built from
`[-Lv; La]` and `koszulC σ J₁` defines a surjective map. -/
theorem surjective_splitMatrix_koszulC (e : ι₂ ⊕ ι₀ ≃ ι₁ ⊕ ι₁) (σ : ι₀ ≃ ι₁ ⊕ δ)
    (τ : ι₁ ≃ ι₂ ⊕ δ) (La Lv : Matrix ι₁ ι₂ T) (J₁ : Matrix ι₁ δ T)
    (h1 : IsUnit ((fromCols La J₁).submatrix id τ).det) :
    Function.Surjective (MMP.Chow.splitMatrix e (fromRows (-Lv) La) (koszulC σ J₁)).mulVec := by
  intro y
  set v := y ∘ e.symm
  set N₁ := (fromCols La J₁).submatrix id τ
  set x := N₁⁻¹ *ᵥ (v ∘ Sum.inr)
  have hx : N₁ *ᵥ x = v ∘ Sum.inr := by
    simp only [x, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h1, Matrix.one_mulVec]
  set w : ι₂ → T := x ∘ τ.symm ∘ Sum.inl
  set z₂ : δ → T := x ∘ τ.symm ∘ Sum.inr
  set z₁ : ι₁ → T := v ∘ Sum.inl + Lv *ᵥ w
  have hN : La *ᵥ w + J₁ *ᵥ z₂ = v ∘ Sum.inr := by
    rw [← hx]
    have hwz : Sum.elim w z₂ = x ∘ τ.symm := Sum.elim_comp_inl_inr (x ∘ τ.symm)
    have : x = Sum.elim w z₂ ∘ τ := by
      rw [hwz]
      funext i
      simp
    rw [this, show N₁ = (fromCols La J₁).submatrix id τ from rfl,
      Matrix.submatrix_mulVec_equiv]
    simp [Function.comp_assoc, Matrix.fromCols_mulVec_sumElim]
  refine ⟨Sum.elim w (Sum.elim z₁ z₂ ∘ σ), ?_⟩
  have h1' : (MMP.Chow.splitMatrix e (fromRows (-Lv) La) (koszulC σ J₁)).mulVec
      (Sum.elim w (Sum.elim z₁ z₂ ∘ σ)) =
      ((fromRows (-Lv) La) *ᵥ w + (koszulC σ J₁) *ᵥ (Sum.elim z₁ z₂ ∘ σ)) ∘ e := by
    rw [MMP.Chow.splitMatrix, Matrix.fromCols_mulVec_sumElim]
    have a1 : ((fromRows (-Lv) La).submatrix e id) *ᵥ w = ((fromRows (-Lv) La) *ᵥ w) ∘ e := by
      simpa using Matrix.submatrix_mulVec_equiv (fromRows (-Lv) La) w e (Equiv.refl _)
    have a2 : ((koszulC σ J₁).submatrix e id) *ᵥ (Sum.elim z₁ z₂ ∘ σ) =
        ((koszulC σ J₁) *ᵥ (Sum.elim z₁ z₂ ∘ σ)) ∘ e := by
      simpa using Matrix.submatrix_mulVec_equiv (koszulC σ J₁) _ e (Equiv.refl _)
    rw [a1, a2]; rfl
  have hC : (koszulC σ J₁) *ᵥ (Sum.elim z₁ z₂ ∘ σ) = Sum.elim z₁ (J₁ *ᵥ z₂) := by
    rw [koszulC, ← Matrix.submatrix_id_id (fromBlocks (1 : Matrix ι₁ ι₁ T) 0 0 J₁)]
    have := Matrix.submatrix_mulVec_equiv (fromBlocks (1 : Matrix ι₁ ι₁ T) 0 0 J₁)
      (Sum.elim z₁ z₂ ∘ σ) (Equiv.refl _) σ
    simp only [Equiv.coe_refl, Function.comp_id] at this
    rw [Matrix.submatrix_id_id, this]
    simp [Function.comp_assoc, Matrix.fromBlocks_mulVec]
  rw [h1', hC]
  funext i
  simp only [Function.comp_apply]
  rcases h : e i with j | j
  · have hi : e.symm (Sum.inl j) = i := by rw [← h]; simp
    simp only [Matrix.fromRows_mulVec, Pi.add_apply, Sum.elim_inl, Matrix.neg_mulVec, z₁, v,
      Function.comp_apply, hi, Pi.neg_apply]
    abel
  · have hi : e.symm (Sum.inr j) = i := by rw [← h]; simp
    simp only [Matrix.fromRows_mulVec, Pi.add_apply, Sum.elim_inr]
    have := congrFun hN j
    simp only [Pi.add_apply, Function.comp_apply] at this
    rw [this]; simp [v, hi]

/-- **The determinant of the Koszul complex at a fixed first hyperplane.**  With `[La | J₁]` and
`[L'a | J₀]` invertible, the determinant of `T^{ι₂} → T^{ι₁} ⊕ T^{ι₁} → T^{ι₀}`,
`w ↦ (-Lv w, La w)`, `(s, t) ↦ L'a s + L'v t`, is a unit times `det [L'a | J₀] · det Y`. -/
theorem exists_complexDet_koszul_eq {K : Type*} [Field K] [Algebra T K]
    (e : ι₂ ⊕ ι₀ ≃ ι₁ ⊕ ι₁) (σ : ι₀ ≃ ι₁ ⊕ δ) (τ : ι₁ ≃ ι₂ ⊕ δ) (La Lv : Matrix ι₁ ι₂ T)
    (L'a L'v : Matrix ι₀ ι₁ T) (J₁ : Matrix ι₁ δ T) (J₀ : Matrix ι₀ δ T)
    (h1 : IsUnit ((fromCols La J₁).submatrix id τ).det)
    (h0 : IsUnit ((fromCols L'a J₀).submatrix id σ).det) (hcomm : L'a * Lv = L'v * La)
    (hY : algebraMap T K (koszulY σ L'a L'v J₁ J₀).det ≠ 0) :
    MMP.Chow.IsSplitExact e ((fromRows (-Lv) La).map (algebraMap T K))
        ((fromCols L'a L'v).map (algebraMap T K)) ∧
    ∃ u : Tˣ, MMP.Chow.complexDet K e (fromRows (-Lv) La) (fromCols L'a L'v) =
      algebraMap T K u * algebraMap T K (koszulY σ L'a L'v J₁ J₀).det := by
  have hBA : fromCols L'a L'v * fromRows (-Lv) La = 0 := by
    rw [fromCols_mul_fromRows, Matrix.mul_neg, hcomm, neg_add_cancel]
  have hdet := det_fromCols_mul_eq σ L'a L'v J₁ J₀ h0
  rw [← fromCols_mul_koszulC] at hdet
  have hD : algebraMap T K (fromCols L'a L'v * koszulC σ J₁).det ≠ 0 := by
    rw [hdet, map_mul]
    exact mul_ne_zero (h0.map _).ne_zero hY
  obtain ⟨hsplit, u, hu⟩ := MMP.Chow.exists_unit_complexDet_eq_det_mul (K := K) hBA (koszulC σ J₁)
    (surjective_splitMatrix_koszulC e σ τ La Lv J₁ h1) hD
  refine ⟨hsplit, u * h0.unit, ?_⟩
  rw [hu, hdet, map_mul, Units.val_mul, map_mul, IsUnit.unit_spec, mul_assoc]

/-- The image of the inverse of a matrix with invertible determinant under a ring homomorphism
is the inverse of its image. -/
theorem map_nonsing_inv {S : Type*} [CommRing S] (f : T →+* S) {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n T) (h : IsUnit M.det) : (M⁻¹).map f = (M.map f)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one _ f.map_zero f.map_one]

/-- If `[L'a | J₀]` is invertible, `koszulY` commutes with applying a ring homomorphism to the
entries. -/
theorem koszulY_map {S : Type*} [CommRing S] (f : T →+* S) (σ : ι₀ ≃ ι₁ ⊕ δ)
    (L'a L'v : Matrix ι₀ ι₁ T) (J₁ : Matrix ι₁ δ T) (J₀ : Matrix ι₀ δ T)
    (h0 : IsUnit ((fromCols L'a J₀).submatrix id σ).det) :
    (koszulY σ L'a L'v J₁ J₀).map f =
      koszulY σ (L'a.map f) (L'v.map f) (J₁.map f) (J₀.map f) := by
  have hQ : (koszulQ σ L'a L'v J₁ J₀).map f =
      koszulQ σ (L'a.map f) (L'v.map f) (J₁.map f) (J₀.map f) := by
    rw [koszulQ, koszulQ, Matrix.map_mul, map_nonsing_inv f _ h0]
    congr 2
    · ext i j; rcases h : σ j with a | a <;> simp [h]
    · ext i j; rcases h : σ j with a | a <;> simp [h, Matrix.mul_apply, map_sum]
  ext i j
  have := congrFun (congrFun hQ (σ.symm (Sum.inr i))) (σ.symm (Sum.inr j))
  simpa [koszulY] using this

end KoszulReduction

section FieldDet

variable {κ : Type*} [Field κ] {ι₂ ι₁ ι₀ δ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]
  [Fintype δ] [DecidableEq ι₂] [DecidableEq ι₁] [DecidableEq ι₀] [DecidableEq δ]
  {M₁ M₀ : Type*} [AddCommGroup M₁] [Module κ M₁] [AddCommGroup M₀] [Module κ M₀]

/-- If `[L | J]` is invertible and `E` is surjective with kernel the range of `L`, then `E ∘ J` is
bijective. -/
theorem bijective_comp_mulVecLin {ι ι' M : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] [AddCommGroup M] [Module κ M] (ρ : ι' ≃ ι ⊕ δ) (L : Matrix ι' ι κ)
    (J : Matrix ι' δ κ) (E : (ι' → κ) →ₗ[κ] M) (hu : IsUnit ((fromCols L J).submatrix id ρ).det)
    (hs : Function.Surjective E) (hk : LinearMap.ker E = LinearMap.range L.mulVecLin) :
    Function.Bijective (E ∘ₗ J.mulVecLin) := by
  have hsurj : ∀ x : ι' → κ, ∃ w z, x = L *ᵥ w + J *ᵥ z := by
    intro x
    have h := (Matrix.mulVec_surjective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 hu)) x
    obtain ⟨y, hy⟩ := h
    refine ⟨y ∘ ρ.symm ∘ Sum.inl, y ∘ ρ.symm ∘ Sum.inr, ?_⟩
    rw [← hy, Matrix.submatrix_mulVec_equiv]
    have : y ∘ ρ.symm = Sum.elim (y ∘ ρ.symm ∘ Sum.inl) (y ∘ ρ.symm ∘ Sum.inr) :=
      (Sum.elim_comp_inl_inr _).symm
    rw [this, Matrix.fromCols_mulVec_sumElim]; rfl
  refine ⟨fun z z' hz => ?_, fun m => ?_⟩
  · rw [← sub_eq_zero]
    have h0 : J *ᵥ (z - z') ∈ LinearMap.ker E := by
      simp only [LinearMap.mem_ker, Matrix.mulVec_sub, map_sub]
      exact sub_eq_zero.2 hz
    rw [hk] at h0
    obtain ⟨w, hw⟩ := h0
    have hinj := Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu)
    have : ((fromCols L J).submatrix id ρ) *ᵥ (Sum.elim (-w) (z - z') ∘ ρ) =
        ((fromCols L J).submatrix id ρ) *ᵥ 0 := by
      rw [Matrix.submatrix_mulVec_equiv, Matrix.mulVec_zero]
      simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
        Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_neg]
      change -(L.mulVecLin w) + _ = 0
      rw [hw]; abel
    funext j
    have h2 := congrFun (hinj this) (ρ.symm (Sum.inr j))
    simpa using h2
  · obtain ⟨x, rfl⟩ := hs m
    obtain ⟨w, z, rfl⟩ := hsurj x
    refine ⟨z, ?_⟩
    have : L *ᵥ w ∈ LinearMap.ker E := hk ▸ ⟨w, rfl⟩
    rw [LinearMap.mem_ker] at this
    simp [this]

/-- **The determinant of the induced map between the quotients.** Over a field, let
`E₁ : κ^{ι₁} → M₁` and `E₀ : κ^{ι₀} → M₀` be surjective with kernels the ranges of `La` and
`L'a`, and let `[La | J₁]` and `[L'a | J₀]` be invertible.  For a fixed isomorphism
`P : M₁ ≃ M₀` there is a nonzero constant `c` with `det Y(L'v) = c · det Φ` whenever
`E₀ ∘ L'v = P ∘ Φ ∘ E₁`. -/
theorem exists_det_koszulY_eq (σ : ι₀ ≃ ι₁ ⊕ δ) (τ : ι₁ ≃ ι₂ ⊕ δ) (La : Matrix ι₁ ι₂ κ)
    (L'a : Matrix ι₀ ι₁ κ) (J₁ : Matrix ι₁ δ κ) (J₀ : Matrix ι₀ δ κ)
    (h1 : IsUnit ((fromCols La J₁).submatrix id τ).det)
    (h0 : IsUnit ((fromCols L'a J₀).submatrix id σ).det)
    (E₁ : (ι₁ → κ) →ₗ[κ] M₁) (E₀ : (ι₀ → κ) →ₗ[κ] M₀) (hE₁ : Function.Surjective E₁)
    (hE₀ : Function.Surjective E₀) (hk₁ : LinearMap.ker E₁ = LinearMap.range La.mulVecLin)
    (hk₀ : LinearMap.ker E₀ = LinearMap.range L'a.mulVecLin) (P : M₁ ≃ₗ[κ] M₀) :
    ∃ c : κ, c ≠ 0 ∧ ∀ (L'v : Matrix ι₀ ι₁ κ) (Φ : M₁ →ₗ[κ] M₁),
      (∀ x, E₀ (L'v *ᵥ x) = P (Φ (E₁ x))) →
        (koszulY σ L'a L'v J₁ J₀).det = c * LinearMap.det Φ := by
  let G₁ := LinearEquiv.ofBijective _ (bijective_comp_mulVecLin τ La J₁ E₁ h1 hE₁ hk₁)
  let G₀ := LinearEquiv.ofBijective _ (bijective_comp_mulVecLin σ L'a J₀ E₀ h0 hE₀ hk₀)
  let c := LinearMap.det (G₀.symm.toLinearMap ∘ₗ P.toLinearMap ∘ₗ G₁.toLinearMap)
  refine ⟨c, ?_, fun L'v Φ hΦ => ?_⟩
  · exact (LinearEquiv.isUnit_det' (G₁.trans (P.trans G₀.symm))).ne_zero
  set Q := koszulQ σ L'a L'v J₁ J₀
  set Y := koszulY σ L'a L'v J₁ J₀
  have hNQ : (fromCols L'a J₀).submatrix id σ * Q = (fromCols L'a (L'v * J₁)).submatrix id σ := by
    show _ * (_⁻¹ * _) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h0, Matrix.one_mul]
  have key : ∀ z : δ → κ, G₀ (Y *ᵥ z) = P (Φ (G₁ z)) := by
    intro z
    set v' : ι₀ → κ := Sum.elim 0 z ∘ σ
    have hM : (fromCols L'a (L'v * J₁)).submatrix id σ *ᵥ v' = L'v *ᵥ (J₁ *ᵥ z) := by
      rw [Matrix.submatrix_mulVec_equiv]
      simp [v', Function.comp_assoc, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_mulVec]
    have hQv : (Q *ᵥ v') ∘ σ.symm = Sum.elim ((Q *ᵥ v') ∘ σ.symm ∘ Sum.inl) (Y *ᵥ z) := by
      rw [← Sum.elim_comp_inl_inr ((Q *ᵥ v') ∘ σ.symm)]
      congr 1
      funext i
      simp only [Function.comp_apply, Matrix.mulVec, dotProduct, v', Y, koszulY, Matrix.of_apply]
      rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
      simp [Q]
    have hN : (fromCols L'a J₀).submatrix id σ *ᵥ (Q *ᵥ v') =
        L'a *ᵥ ((Q *ᵥ v') ∘ σ.symm ∘ Sum.inl) + J₀ *ᵥ (Y *ᵥ z) := by
      rw [Matrix.submatrix_mulVec_equiv, hQv, Matrix.fromCols_mulVec_sumElim]; rfl
    rw [Matrix.mulVec_mulVec, hNQ, hM] at hN
    have h1 := hΦ (J₁ *ᵥ z)
    rw [hN, map_add] at h1
    have hz : E₀ (L'a *ᵥ ((Q *ᵥ v') ∘ σ.symm ∘ Sum.inl)) = 0 := by
      rw [← LinearMap.mem_ker, hk₀]; exact ⟨_, rfl⟩
    rw [hz, zero_add] at h1
    exact h1
  have hlin : Matrix.toLin' Y = (G₀.symm.toLinearMap ∘ₗ P.toLinearMap ∘ₗ G₁.toLinearMap) ∘ₗ
      (G₁.symm.toLinearMap ∘ₗ Φ ∘ₗ G₁.toLinearMap) := by
    refine LinearMap.ext fun z => ?_
    show Y *ᵥ z = G₀.symm (P (G₁ (G₁.symm (Φ (G₁ z)))))
    rw [LinearEquiv.apply_symm_apply, ← key z, LinearEquiv.symm_apply_apply]
  rw [← LinearMap.det_toLin', hlin, LinearMap.det_comp]
  congr 1
  exact LinearMap.det_conj Φ G₁.symm

end FieldDet

end BB

section RestrictedDet

open Matrix

/-- **The determinant of the Koszul complex at a fixed first hyperplane, as a polynomial in the
second.** Over a field `κ`, let `X₁ i`, `X₀ i` be the matrices of a commuting family of
multiplications `V₂ → V₁ → V₀` with `rank V₁ = rank V₂ + d`, `rank V₀ = rank V₁ + d`, and let
`La`, `L'a` be injective members of their span. If the cokernels of `La`, `L'a` are identified with
spaces `M₁`, `M₀`, with `M₁ ≃ M₀`, and the endomorphism of `M₁` induced by `∑ bᵢ X₀ i` has
determinant `Q(b)` for a nonzero polynomial `Q`, then the Koszul complex of `(La, ∑ vᵢ X i)` over
`κ[v]` is generically split exact and its determinant is a nonzero constant times `Q`. -/
theorem isSplitExact_and_exists_complexDet_eq_C_mul {κ : Type*} [Field κ] [Infinite κ] {σv : Type*}
    [Fintype σv] {r₂ r₁ r₀ d : ℕ} (h₁ : r₁ = r₂ + d) (h₀ : r₀ = r₁ + d)
    (e : Fin r₂ ⊕ Fin r₀ ≃ Fin r₁ ⊕ Fin r₁)
    (X₁ : σv → Matrix (Fin r₁) (Fin r₂) κ) (X₀ : σv → Matrix (Fin r₀) (Fin r₁) κ)
    (La : Matrix (Fin r₁) (Fin r₂) κ) (L'a : Matrix (Fin r₀) (Fin r₁) κ)
    (hcomm : ∀ i, L'a * X₁ i = X₀ i * La)
    (hLa : Function.Injective La.mulVec) (hL'a : Function.Injective L'a.mulVec)
    {M₁ M₀ : Type*} [AddCommGroup M₁] [Module κ M₁] [AddCommGroup M₀] [Module κ M₀]
    (E₁ : (Fin r₁ → κ) →ₗ[κ] M₁) (E₀ : (Fin r₀ → κ) →ₗ[κ] M₀) (hE₁ : Function.Surjective E₁)
    (hE₀ : Function.Surjective E₀) (hk₁ : LinearMap.ker E₁ = LinearMap.range La.mulVecLin)
    (hk₀ : LinearMap.ker E₀ = LinearMap.range L'a.mulVecLin) (P : M₁ ≃ₗ[κ] M₀)
    (Φ : (σv → κ) → M₁ →ₗ[κ] M₁)
    (hΦ : ∀ b x, E₀ ((∑ i, b i • X₀ i) *ᵥ x) = P (Φ b (E₁ x)))
    (Q : MvPolynomial σv κ) (hQ : ∀ b, eval b Q = LinearMap.det (Φ b)) (hQ0 : Q ≠ 0) :
    MMP.Chow.IsSplitExact e
        ((fromRows (-(∑ i, (X i : MvPolynomial σv κ) • (X₁ i).map (C (σ := σv))))
            (La.map (C (σ := σv)))).map
          (algebraMap _ (FractionRing (MvPolynomial σv κ))))
        ((fromCols (L'a.map (C (σ := σv)))
            (∑ i, (X i : MvPolynomial σv κ) • (X₀ i).map (C (σ := σv)))).map
          (algebraMap _ (FractionRing (MvPolynomial σv κ)))) ∧
    ∃ c : κ, c ≠ 0 ∧ MMP.Chow.complexDet (FractionRing (MvPolynomial σv κ)) e
        (fromRows (-(∑ i, (X i : MvPolynomial σv κ) • (X₁ i).map (C (σ := σv))))
          (La.map (C (σ := σv))))
        (fromCols (L'a.map (C (σ := σv)))
          (∑ i, (X i : MvPolynomial σv κ) • (X₀ i).map (C (σ := σv)))) =
      algebraMap _ (FractionRing (MvPolynomial σv κ)) (C c * Q) := by
  classical
  set Lv : Matrix (Fin r₁) (Fin r₂) (MvPolynomial σv κ) :=
    ∑ i, (X i : MvPolynomial σv κ) • (X₁ i).map (C (σ := σv)) with hLv
  set L'v : Matrix (Fin r₀) (Fin r₁) (MvPolynomial σv κ) :=
    ∑ i, (X i : MvPolynomial σv κ) • (X₀ i).map (C (σ := σv)) with hL'v
  let τ : Fin r₁ ≃ Fin r₂ ⊕ Fin d := (finCongr h₁).trans finSumFinEquiv.symm
  let σ : Fin r₀ ≃ Fin r₁ ⊕ Fin d := (finCongr h₀).trans finSumFinEquiv.symm
  obtain ⟨J₁, hJ₁⟩ := exists_isUnit_det_fromCols La hLa τ
  obtain ⟨J₀, hJ₀⟩ := exists_isUnit_det_fromCols L'a hL'a σ
  have hdetC : ∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n κ), IsUnit M.det →
      IsUnit (M.map (C (σ := σv))).det := fun M hM => by
    have h := RingHom.map_det (C : κ →+* MvPolynomial σv κ) M
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact hM.map _
  have h1 :
      IsUnit ((fromCols (La.map (C (σ := σv))) (J₁.map (C (σ := σv)))).submatrix id τ).det := by
    rw [← fromCols_map, submatrix_map]
    exact hdetC _ hJ₁
  have h0 :
      IsUnit ((fromCols (L'a.map (C (σ := σv))) (J₀.map (C (σ := σv)))).submatrix id σ).det := by
    rw [← fromCols_map, submatrix_map]
    exact hdetC _ hJ₀
  have hcommT : L'a.map (C (σ := σv)) * Lv = L'v * La.map (C (σ := σv)) := by
    simp only [hLv, hL'v, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.map_mul, hcomm]
  obtain ⟨c, hc, hdet⟩ := exists_det_koszulY_eq σ τ La L'a J₁ J₀ hJ₁ hJ₀ E₁ E₀ hE₁ hE₀ hk₁ hk₀ P
  have hY : (koszulY σ (L'a.map (C (σ := σv))) L'v (J₁.map (C (σ := σv)))
      (J₀.map (C (σ := σv)))).det = C c * Q := by
    refine MvPolynomial.funext fun b => ?_
    have hm := koszulY_map (MvPolynomial.eval b) σ (L'a.map (C (σ := σv))) L'v
      (J₁.map (C (σ := σv))) (J₀.map (C (σ := σv))) h0
    have e1 : (L'a.map (C (σ := σv))).map (MvPolynomial.eval b) = L'a := by ext i j; simp
    have e2 : (J₁.map (C (σ := σv))).map (MvPolynomial.eval b) = J₁ := by ext i j; simp
    have e3 : (J₀.map (C (σ := σv))).map (MvPolynomial.eval b) = J₀ := by ext i j; simp
    have hL'b : L'v.map (MvPolynomial.eval b) = ∑ i, b i • X₀ i := by
      ext i j; simp [hL'v, Matrix.sum_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, e1, e2, e3, hL'b,
      hdet _ (Φ b) (hΦ b), map_mul, eval_C, hQ]
  have hYne : algebraMap (MvPolynomial σv κ) (FractionRing (MvPolynomial σv κ))
      (koszulY σ (L'a.map (C (σ := σv))) L'v (J₁.map (C (σ := σv)))
        (J₀.map (C (σ := σv)))).det ≠ 0 := by
    rw [hY, Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact mul_ne_zero (C_ne_zero.2 hc) hQ0
  obtain ⟨hsplit, u, hu⟩ :=
    exists_complexDet_koszul_eq (K := FractionRing (MvPolynomial σv κ)) e σ τ
      (La.map (C (σ := σv))) Lv (L'a.map (C (σ := σv))) L'v (J₁.map (C (σ := σv)))
      (J₀.map (C (σ := σv))) h1 h0 hcommT hYne
  obtain ⟨u₀, hu₀, hu₀'⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 u.isUnit
  refine ⟨hsplit, u₀ * c, mul_ne_zero hu₀.ne_zero hc, ?_⟩
  rw [hu, hY, hu₀', ← map_mul, ← mul_assoc, ← C_mul]

end RestrictedDet

open TopCat TopCat.Presheaf TopologicalSpace Opposite in
/-- **Gluing preimages along a stalkwise injective morphism.** A section of `G` whose germs all
lie in the images of the stalk maps of a stalkwise injective morphism `F ⟶ G` of sheaves of abelian
groups is the image of a section of `F`. -/
theorem exists_app_eq_of_germ_mem_range {X : TopCat.{u}} {F G : TopCat.Sheaf Ab.{u} X}
    (f : F ⟶ G) (U : Opens X)
    (hinj : ∀ x ∈ U, Function.Injective ((stalkFunctor Ab x).map f.1))
    (t : ToType (G.1.obj (op U)))
    (ht : ∀ x (hx : x ∈ U), G.presheaf.germ U x hx t ∈
      Set.range ((stalkFunctor Ab x).map f.1)) :
    ∃ s, f.1.app (op U) s = t := by
  have hsurj : ∀ x : U, ∃ (V : Opens X) (_ : x.1 ∈ V) (iVU : V ⟶ U)
      (s : ToType (F.1.obj (op V))), f.1.app (op V) s = G.1.map iVU.op t := by
    intro x
    obtain ⟨s₀, hs₀⟩ := ht x.1 x.2
    obtain ⟨V₁, hxV₁, s₁, rfl⟩ := F.presheaf.exists_germ_eq s₀
    rw [stalkFunctor_map_germ_apply V₁ x.1 hxV₁ f.1 s₁] at hs₀
    obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ := G.presheaf.germ_eq x.1 hxV₁ x.2 _ _ hs₀
    refine ⟨V₂, hxV₂, iV₂U, F.1.map iV₂V₁.op s₁, ?_⟩
    rw [← ConcreteCategory.comp_apply, f.1.naturality, ConcreteCategory.comp_apply, heq]
  choose V mV iVU sf heq using hsurj
  have V_cover : U ≤ iSup V := fun x hxU => Opens.mem_iSup.2 ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩
  suffices IsCompatible F.obj V sf by
    obtain ⟨s, s_spec, -⟩ := F.existsUnique_gluing' V U iVU V_cover sf this
    refine ⟨s, ?_⟩
    apply G.eq_of_locally_eq' V U iVU V_cover
    intro x
    rw [← ConcreteCategory.comp_apply, ← f.1.naturality, ConcreteCategory.comp_apply, s_spec, heq]
  intro x y
  apply section_ext
  intro z hz
  apply hinj z ((iVU x).le ((inf_le_left : V x ⊓ V y ≤ V x) hz))
  rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply]
  simp_rw [← ConcreteCategory.comp_apply, f.1.naturality, ConcreteCategory.comp_apply, heq,
    ← ConcreteCategory.comp_apply, ← G.1.map_comp]
  rfl

/-- The scheme-module form of `exists_app_eq_of_germ_mem_range`. -/
theorem exists_app_eq_of_germ_mem_range_stalkLinearMap {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens)
    (hinj : ∀ y ∈ U, Function.Injective (stalkLinearMap M N φ y)) (t : Γ(N, U))
    (ht : ∀ y (hy : y ∈ U), N.presheaf.germ U y hy t ∈ Set.range (stalkLinearMap M N φ y)) :
    ∃ s, φ.app U s = t :=
  exists_app_eq_of_germ_mem_range (F := ⟨M.presheaf, M.isSheaf⟩) (G := ⟨N.presheaf, N.isSheaf⟩)
    ⟨φ.mapPresheaf⟩ U hinj t ht

/-- A morphism of modules injective on stalks is injective on sections. -/
theorem app_injective_of_stalkLinearMap_injective {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens) (hinj : ∀ y ∈ U, Function.Injective (stalkLinearMap M N φ y)) :
    Function.Injective (φ.app U) :=
  TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (F := ⟨M.presheaf, M.isSheaf⟩)
    (G := N.presheaf) φ.mapPresheaf U hinj

section StalkCoker

variable {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)

/-- The cokernel of the stalk map of `φ` at `y`. -/
abbrev stalkCoker (y : X) :=
  N.presheaf.stalk y ⧸ LinearMap.range (stalkLinearMap M N φ y)

/-- The classes of the germs of a global section in the stalk cokernels of `φ` at the points of
`Z`. -/
noncomputable def germCoker (Z : Finset X) : Γ(N, ⊤) →+ ∀ y : Z, stalkCoker φ y where
  toFun s y := Submodule.Quotient.mk ((N.presheaf.Γgerm y).hom s)
  map_zero' := by ext y; simp
  map_add' s s' := by ext y; simp

/-- The value of `germCoker φ Z s` at `y` is the class of the germ of `s` at `y`. -/
theorem germCoker_apply (Z : Finset X) (s : Γ(N, ⊤)) (y : Z) :
    germCoker φ Z s y = Submodule.Quotient.mk ((N.presheaf.Γgerm y).hom s) := rfl

/-- **The kernel of the germ map.** If the stalk maps of `φ` are injective everywhere and
surjective off `Z`, a global section has zero classes at `Z` exactly when it lies in the image of
`φ`. -/
theorem germCoker_eq_zero_iff (Z : Finset X)
    (hinj : ∀ y, Function.Injective (stalkLinearMap M N φ y))
    (hsurj : ∀ y, y ∉ Z → Function.Surjective (stalkLinearMap M N φ y)) (s : Γ(N, ⊤)) :
    germCoker φ Z s = 0 ↔ ∃ w, φ.app ⊤ w = s := by
  constructor
  · intro h
    refine exists_app_eq_of_germ_mem_range_stalkLinearMap φ ⊤ (fun y _ => hinj y) s fun y _ => ?_
    by_cases hy : y ∈ Z
    · have := congrFun h ⟨y, hy⟩
      rw [germCoker_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    · exact hsurj y hy _
  · rintro ⟨w, rfl⟩
    ext y
    rw [germCoker_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨(M.presheaf.Γgerm y).hom w, stalkLinearMap_germ M N φ ⊤ y trivial w⟩

end StalkCoker

/-- **The determinant of a product of endomorphisms** of a finite family of finite-dimensional
spaces is the product of their determinants. -/
theorem det_pi_comp_proj {K : Type*} {ι : Type v} [Field K] [Fintype ι] [DecidableEq ι]
    {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, FiniteDimensional K (M i)] (f : ∀ i, M i →ₗ[K] M i) :
    LinearMap.det (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) = ∏ i, LinearMap.det (f i) := by
  suffices H : ∀ (n : ℕ) {ι : Type v} [Fintype ι] [DecidableEq ι],
      Fintype.card ι = n → ∀ {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
      [∀ i, FiniteDimensional K (M i)] (f : ∀ i, M i →ₗ[K] M i),
      LinearMap.det (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) = ∏ i, LinearMap.det (f i) from
    H _ rfl f
  intro n
  induction n with
  | zero =>
    intro ι _ _ hc M _ _ _ f
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [LinearMap.det_eq_one_of_subsingleton]
  | succ n ih =>
    intro ι _ _ hc M _ _ _ f
    obtain ⟨y⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    let e : ((∀ i : {i // i = y}, M i) × (∀ i : {i // ¬ i = y}, M i)) ≃ₗ[K] (∀ i, M i) :=
      LinearEquiv.symm { Equiv.piEquivPiSubtypeProd (fun i => i = y) M with
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    let g₁ : (∀ i : {i // i = y}, M i) →ₗ[K] (∀ i : {i // i = y}, M i) :=
      LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i
    let g₂ : (∀ i : {i // ¬ i = y}, M i) →ₗ[K] (∀ i : {i // ¬ i = y}, M i) :=
      LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i
    have hconj : LinearMap.pi (fun i => f i ∘ₗ LinearMap.proj i) =
        e.toLinearMap ∘ₗ (g₁.prodMap g₂) ∘ₗ e.symm.toLinearMap := by
      refine LinearMap.ext fun v => funext fun i => ?_
      by_cases h : i = y
      · subst h; simp [e, g₁, g₂, Equiv.piEquivPiSubtypeProd]
      · simp [e, g₁, g₂, Equiv.piEquivPiSubtypeProd, h]
    have h2 := ih (ι := {i // ¬ i = y}) (by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega) (fun i => f i)
    have h1 : LinearMap.det g₁ = LinearMap.det (f y) := by
      letI u : Unique {i // i = y} := ⟨⟨⟨y, rfl⟩⟩, fun i => Subtype.ext i.2⟩
      let e' := LinearEquiv.piUnique K (fun i : {i // i = y} => M i)
      have : g₁ = e'.symm.toLinearMap ∘ₗ f y ∘ₗ e'.toLinearMap := by
        refine LinearMap.ext fun v => funext fun i => ?_
        obtain ⟨i, rfl⟩ := i
        rfl
      rw [this]
      exact LinearMap.det_conj (f y) e'.symm
    rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, h1, h2,
      Fintype.prod_eq_mul_prod_subtype_ne _ y]

section StalkCokerStructure

variable {X : Scheme.{u}}

/-- **The stalk cokernel of a multiple of an isomorphism.** If the stalk map of `φ` at `y` is `r`
times a surjection onto a free module of rank one, its cokernel is `𝒪_{X,y} / (r)`. -/
theorem nonempty_stalkCoker_equiv {M N : X.Modules} (φ ψ : M ⟶ N) (y : X)
    (r : X.presheaf.stalk y) (h : stalkLinearMap M N φ y = r • stalkLinearMap M N ψ y)
    (hψ : Function.Surjective (stalkLinearMap M N ψ y)) {n : N.presheaf.stalk y}
    (hn : Stacks.Divisors.IsStalkBasis N y n) :
    Nonempty (stalkCoker φ y ≃ₗ[X.presheaf.stalk y] X.presheaf.stalk y ⧸ Ideal.span {r}) := by
  have hrange : Submodule.map hn.linearEquiv.toLinearMap
      (Ideal.span {r} : Submodule (X.presheaf.stalk y) (X.presheaf.stalk y)) =
      LinearMap.range (stalkLinearMap M N φ y) := by
    ext m
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe,
      Stacks.Divisors.IsStalkBasis.linearEquiv_apply, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      obtain ⟨m₁, hm₁⟩ := hψ n
      refine ⟨s • m₁, ?_⟩
      rw [h, LinearMap.smul_apply, map_smul, hm₁, smul_smul, mul_comm]
    · rintro ⟨m₀, rfl⟩
      obtain ⟨s, hs⟩ := hn.surjective (stalkLinearMap M N ψ y m₀)
      refine ⟨s * r, ⟨s, rfl⟩, ?_⟩
      rw [h, LinearMap.smul_apply, ← hs]
      show (s * r) • n = r • s • n
      rw [smul_smul, mul_comm]
  exact ⟨(Submodule.Quotient.equiv _ _ hn.linearEquiv hrange).symm⟩

/-- **Commuting isomorphisms identify stalk cokernels.** -/
noncomputable def stalkCokerEquiv {M₂ M₁ M₀ : X.Modules} (α₁ : M₂ ⟶ M₁) (α₀ : M₁ ⟶ M₀)
    (τ₂ : M₂ ⟶ M₁) (τ₁ : M₁ ⟶ M₀) (y : X) (hcomm : α₁ ≫ τ₁ = τ₂ ≫ α₀)
    (h₂ : Function.Bijective (stalkLinearMap M₂ M₁ τ₂ y))
    (h₁ : Function.Bijective (stalkLinearMap M₁ M₀ τ₁ y)) :
    stalkCoker α₁ y ≃ₗ[X.presheaf.stalk y] stalkCoker α₀ y :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective _ h₁) (by
    ext m
    simp only [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨stalkLinearMap M₂ M₁ τ₂ y w, ?_⟩
      show stalkLinearMap M₁ M₀ α₀ y (stalkLinearMap M₂ M₁ τ₂ y w) =
        stalkLinearMap M₁ M₀ τ₁ y (stalkLinearMap M₂ M₁ α₁ y w)
      rw [← Scheme.Modules.stalkLinearMap_comp τ₂ α₀, ← Scheme.Modules.stalkLinearMap_comp α₁ τ₁,
        hcomm]
    · rintro ⟨w, rfl⟩
      obtain ⟨w', rfl⟩ := h₂.2 w
      refine ⟨stalkLinearMap M₂ M₁ α₁ y w', ⟨w', rfl⟩, ?_⟩
      show stalkLinearMap M₁ M₀ τ₁ y (stalkLinearMap M₂ M₁ α₁ y w') =
        stalkLinearMap M₁ M₀ α₀ y (stalkLinearMap M₂ M₁ τ₂ y w')
      rw [← Scheme.Modules.stalkLinearMap_comp τ₂ α₀, ← Scheme.Modules.stalkLinearMap_comp α₁ τ₁,
        hcomm])

/-- `stalkCokerEquiv` sends the class of `m` to the class of its image under the stalk map
of `τ₁`. -/
theorem stalkCokerEquiv_mk {M₂ M₁ M₀ : X.Modules} (α₁ : M₂ ⟶ M₁) (α₀ : M₁ ⟶ M₀)
    (τ₂ : M₂ ⟶ M₁) (τ₁ : M₁ ⟶ M₀) (y : X) (hcomm : α₁ ≫ τ₁ = τ₂ ≫ α₀)
    (h₂ : Function.Bijective (stalkLinearMap M₂ M₁ τ₂ y))
    (h₁ : Function.Bijective (stalkLinearMap M₁ M₀ τ₁ y)) (m : M₁.presheaf.stalk y) :
    stalkCokerEquiv α₁ α₀ τ₂ τ₁ y hcomm h₂ h₁ (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (stalkLinearMap M₁ M₀ τ₁ y m) := rfl

end StalkCokerStructure

/-- **Bases after a base change.** Bases of three modules `Pᵢ ≃ Mᵢ` over `R` give bases of their
base changes `Nᵢ` to `K` in which every map induced by a linear map has, as matrix, the image of
the matrix of that map. -/
theorem exists_bases_toMatrix_of_isBaseChange {R K : Type*} [CommRing R] [Field K]
    {_ : Algebra R K} {M₂ M₁ M₀ P₂ P₁ P₀ N₂ N₁ N₀ : Type*}
    [AddCommGroup M₂] [AddCommGroup M₁] [AddCommGroup M₀]
    [AddCommGroup P₂] [AddCommGroup P₁] [AddCommGroup P₀]
    [AddCommGroup N₂] [AddCommGroup N₁] [AddCommGroup N₀]
    {_ : Module R M₂} {_ : Module R M₁} {_ : Module R M₀}
    {_ : Module R P₂} {_ : Module R P₁} {_ : Module R P₀}
    {_ : Module R N₂} {_ : Module R N₁} {_ : Module R N₀}
    {_ : Module K N₂} {_ : Module K N₁} {_ : Module K N₀}
    {_ : IsScalarTower R K N₂} {_ : IsScalarTower R K N₁} {_ : IsScalarTower R K N₀}
    {β₂ : M₂ →ₗ[R] N₂} {β₁ : M₁ →ₗ[R] N₁} {β₀ : M₀ →ₗ[R] N₀}
    (h₂ : IsBaseChange K β₂) (h₁ : IsBaseChange K β₁) (h₀ : IsBaseChange K β₀)
    (e₂ : M₂ ≃ₗ[R] P₂) (e₁ : M₁ ≃ₗ[R] P₁) (e₀ : M₀ ≃ₗ[R] P₀)
    {r₂ r₁ r₀ : ℕ} (b₂ : Module.Basis (Fin r₂) R P₂) (b₁ : Module.Basis (Fin r₁) R P₁)
    (b₀ : Module.Basis (Fin r₀) R P₀) :
    ∃ (B₂ : Module.Basis (Fin r₂) K N₂) (B₁ : Module.Basis (Fin r₁) K N₁)
      (B₀ : Module.Basis (Fin r₀) K N₀),
      (∀ (φ : M₂ →ₗ[R] M₁) (χ : P₂ →ₗ[R] P₁), (∀ m, e₁ (φ m) = χ (e₂ m)) →
        ∀ (ψ : N₂ →+ N₁) (hs : ∀ (c : K) x, ψ (c • x) = c • ψ x), (∀ m, ψ (β₂ m) = β₁ (φ m)) →
          LinearMap.toMatrix B₂ B₁ (linOfSmul ψ hs) = (LinearMap.toMatrix b₂ b₁ χ).map
            (algebraMap R K)) ∧
      (∀ (φ : M₁ →ₗ[R] M₀) (χ : P₁ →ₗ[R] P₀), (∀ m, e₀ (φ m) = χ (e₁ m)) →
        ∀ (ψ : N₁ →+ N₀) (hs : ∀ (c : K) x, ψ (c • x) = c • ψ x), (∀ m, ψ (β₁ m) = β₀ (φ m)) →
          LinearMap.toMatrix B₁ B₀ (linOfSmul ψ hs) = (LinearMap.toMatrix b₁ b₀ χ).map
            (algebraMap R K)) := by
  refine ⟨h₂.basis (b₂.map e₂.symm), h₁.basis (b₁.map e₁.symm), h₀.basis (b₀.map e₀.symm),
    fun φ χ hχ ψ hs hc => ?_, fun φ χ hχ ψ hs hc => ?_⟩
  · rw [toMatrix_isBaseChange h₂ h₁ _ _ φ (linOfSmul ψ hs) hc, toMatrix_map_symm e₂ e₁ b₂ b₁ φ χ hχ]
  · rw [toMatrix_isBaseChange h₁ h₀ _ _ φ (linOfSmul ψ hs) hc, toMatrix_map_symm e₁ e₀ b₁ b₀ φ χ hχ]

attribute [local instance 10000] HasDerivedCategory.standard in
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
  AlgebraicGeometry.ProperFlatFibreEulerCharacteristic in
/-- **Bases of the fibre sections.** Over an affine open `V` on which the direct images of three
invertible modules are free with bases `bᵢ` and have no higher cohomology, the sections over the
fibre at `t ∈ V` have bases over `κ(t)` in which every morphism of the modules has, as matrix,
the reduction at `t` of the matrix of its direct image. -/
theorem exists_fibreBases {Y T : Scheme.{u}} (π : Y ⟶ T) [IsProper π] [Flat π]
    {V : T.Opens} (hV : IsAffineOpen V) (N₂ N₁ N₀ : Y.Modules)
    (hN₂ : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N₂)
    (hN₁ : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N₁)
    (hN₀ : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N₀)
    (hv₂ : ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₂)))
    (hv₁ : ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₁)))
    (hv₀ : ∀ p : ℕ, 0 < p → Subsingleton
      (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₀)))
    {r₂ r₁ r₀ : ℕ} (b₂ : Module.Basis (Fin r₂) Γ(T, V) Γ((Scheme.Modules.pushforward π).obj N₂, V))
    (b₁ : Module.Basis (Fin r₁) Γ(T, V) Γ((Scheme.Modules.pushforward π).obj N₁, V))
    (b₀ : Module.Basis (Fin r₀) Γ(T, V) Γ((Scheme.Modules.pushforward π).obj N₀, V))
    (t : T) (ht : t ∈ V) :
    letI : Module (T.residueField t) Γ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₂), fiberιOfMem π t ht ⁻¹ᵁ ⊤) :=
      Stacks.Cech.sectionsModule (π.fiberToSpecResidueField t)
        ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj
          ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₂)) (fiberιOfMem π t ht ⁻¹ᵁ ⊤)
    letI : Module (T.residueField t) Γ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₁), fiberιOfMem π t ht ⁻¹ᵁ ⊤) :=
      Stacks.Cech.sectionsModule (π.fiberToSpecResidueField t)
        ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj
          ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₁)) (fiberιOfMem π t ht ⁻¹ᵁ ⊤)
    letI : Module (T.residueField t) Γ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₀), fiberιOfMem π t ht ⁻¹ᵁ ⊤) :=
      Stacks.Cech.sectionsModule (π.fiberToSpecResidueField t)
        ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj
          ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₀)) (fiberιOfMem π t ht ⁻¹ᵁ ⊤)
    ∃ (β₂ : Module.Basis (Fin r₂) (T.residueField t) Γ((Scheme.Modules.pullback
        (fiberιOfMem π t ht)).obj ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₂),
          fiberιOfMem π t ht ⁻¹ᵁ ⊤))
      (β₁ : Module.Basis (Fin r₁) (T.residueField t) Γ((Scheme.Modules.pullback
        (fiberιOfMem π t ht)).obj ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₁),
          fiberιOfMem π t ht ⁻¹ᵁ ⊤))
      (β₀ : Module.Basis (Fin r₀) (T.residueField t) Γ((Scheme.Modules.pullback
        (fiberιOfMem π t ht)).obj ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj N₀),
          fiberιOfMem π t ht ⁻¹ᵁ ⊤)),
      (∀ α : N₂ ⟶ N₁, LinearMap.toMatrix β₂ β₁ (linOfSmul (((Scheme.Modules.pullback
          (fiberιOfMem π t ht)).map ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).map α)).app
            (fiberιOfMem π t ht ⁻¹ᵁ ⊤)).hom (fun c x => Scheme.Modules.Hom.app_smul _ _ _)) =
        (LinearMap.toMatrix b₂ b₁ (MMP.Chow.directImageSectionsMap π V α)).map
          (residueOfMem t ht).hom) ∧
      (∀ α : N₁ ⟶ N₀, LinearMap.toMatrix β₁ β₀ (linOfSmul (((Scheme.Modules.pullback
          (fiberιOfMem π t ht)).map ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).map α)).app
            (fiberιOfMem π t ht ⁻¹ᵁ ⊤)).hom (fun c x => Scheme.Modules.Hom.app_smul _ _ _)) =
        (LinearMap.toMatrix b₁ b₀ (MMP.Chow.directImageSectionsMap π V α)).map
          (residueOfMem t ht).hom) := by
  set ι := (π ⁻¹ᵁ V).ι
  set f := (π ∣_ V) ≫ hV.isoSpec.hom
  set g := fiberιOfMem π t ht
  haveI : Flat f := inferInstance
  have hflat : ∀ L : Y.Modules, Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L →
      ((Scheme.Modules.pullback ι).obj L).IsQuasicoherent ∧
        IsFlatOver f.toLRSHom.toShHom ((Scheme.Modules.pullback ι).obj L) := fun L hL => by
    have hF : Stacks.SheafOfModules.IsInvertible (π ⁻¹ᵁ V).toScheme.presheaf
        (π ⁻¹ᵁ V).toScheme.ringCatSheaf.2 ((Scheme.Modules.pullback ι).obj L) :=
      Stacks.RingedSpace.modulePullback_isInvertible_of ι.toLRSHom.toShHom L hL
    haveI := Stacks.Picard.isQuasicoherent_of_isInvertible _ hF
    exact ⟨inferInstance, (isFinitePresentation_and_isFlatOver_of_isInvertible f _ hF).2⟩
  obtain ⟨hq₂, hf₂⟩ := hflat N₂ hN₂
  obtain ⟨hq₁, hf₁⟩ := hflat N₁ hN₁
  obtain ⟨hq₀, hf₀⟩ := hflat N₀ hN₀
  obtain ⟨-, h₂⟩ := cohomologyBaseChange_of_vanishing f _ hf₂ hv₂ (residueOfMem t ht).hom
    (isPullback_fiberιOfMem π hV t ht)
  obtain ⟨-, h₁⟩ := cohomologyBaseChange_of_vanishing f _ hf₁ hv₁ (residueOfMem t ht).hom
    (isPullback_fiberιOfMem π hV t ht)
  obtain ⟨-, h₀⟩ := cohomologyBaseChange_of_vanishing f _ hf₀ hv₀ (residueOfMem t ht).hom
    (isPullback_fiberιOfMem π hV t ht)
  letI := Stacks.Cech.sectionsModule f ((Scheme.Modules.pullback ι).obj N₂) ⊤
  letI := Stacks.Cech.sectionsModule f ((Scheme.Modules.pullback ι).obj N₁) ⊤
  letI := Stacks.Cech.sectionsModule f ((Scheme.Modules.pullback ι).obj N₀) ⊤
  obtain ⟨B₂, B₁, B₀, hB, hB'⟩ := exists_bases_toMatrix_of_isBaseChange h₂ h₁ h₀
    (restrSecₗ π hV N₂) (restrSecₗ π hV N₁) (restrSecₗ π hV N₀) b₂ b₁ b₀
  exact ⟨B₂, B₁, B₀, fun α => hB (linOfSmul (((Scheme.Modules.pullback ι).map α).app ⊤).hom
      (fun c x => Scheme.Modules.Hom.app_smul _ _ _)) (MMP.Chow.directImageSectionsMap π V α)
      (fun m => restrSec_natural π V α m) _ _
      (fun m => (unit_naturality_apply g _ ⊤ m).symm),
    fun α => hB' (linOfSmul (((Scheme.Modules.pullback ι).map α).app ⊤).hom
      (fun c x => Scheme.Modules.Hom.app_smul _ _ _)) (MMP.Chow.directImageSectionsMap π V α)
      (fun m => restrSec_natural π V α m) _ _
      (fun m => (unit_naturality_apply g _ ⊤ m).symm)⟩

section CokerDet

/-- **Cokernel data for the restricted Koszul determinant.** The cokernels of `La` and `L'a` are
identified with `κ`-spaces `M₁ ≃ M₀` on which the second hyperplane `∑ bᵢ Y₀ i` acts through an
endomorphism of `M₁` of determinant `Q(b)`. -/
def HasCokerDet {κ : Type u} [Field κ] {σv : Type*} [Fintype σv] {r₂ r₁ r₀ : ℕ}
    (Y₀ : σv → Matrix (Fin r₀) (Fin r₁) κ) (La : Matrix (Fin r₁) (Fin r₂) κ)
    (L'a : Matrix (Fin r₀) (Fin r₁) κ) (Q : MvPolynomial σv κ) : Prop :=
  ∃ (M₁ M₀ : Type u) (_ : AddCommGroup M₁) (_ : Module κ M₁) (_ : AddCommGroup M₀)
    (_ : Module κ M₀) (E₁ : (Fin r₁ → κ) →ₗ[κ] M₁) (E₀ : (Fin r₀ → κ) →ₗ[κ] M₀)
    (P : M₁ ≃ₗ[κ] M₀) (Φ : (σv → κ) → M₁ →ₗ[κ] M₁),
    Function.Surjective E₁ ∧ Function.Surjective E₀ ∧
    LinearMap.ker E₁ = LinearMap.range La.mulVecLin ∧
    LinearMap.ker E₀ = LinearMap.range L'a.mulVecLin ∧
    (∀ b v, E₀ (Matrix.mulVec (∑ i, b i • Y₀ i) v) = P (Φ b (E₁ v))) ∧
    ∀ b, eval b Q = LinearMap.det (Φ b)

/-- The `κ`-algebra structure of the stalks of a scheme with a ring map `κ → Γ(X, ⊤)`. -/
noncomputable abbrev stalkAlgebra {X : Scheme.{u}} {κ : Type u} [Field κ]
    (ω : κ →+* Γ(X, ⊤)) (y : X) : Algebra κ (X.presheaf.stalk y) :=
  ((X.presheaf.Γgerm y).hom.comp ω).toAlgebra

/-- A morphism of modules as a `κ`-linear map on global sections. -/
noncomputable def appTopₗ {X : Scheme.{u}} {κ : Type u} [Field κ] (ω : κ →+* Γ(X, ⊤))
    {M N : X.Modules} [Module κ Γ(M, ⊤)] [Module κ Γ(N, ⊤)]
    (hM : ∀ (c : κ) (s : Γ(M, ⊤)), c • s = ω c • s) (hN : ∀ (c : κ) (s : Γ(N, ⊤)), c • s = ω c • s)
    (φ : M ⟶ N) : Γ(M, ⊤) →ₗ[κ] Γ(N, ⊤) :=
  linOfSmul (φ.app ⊤).hom (fun c s => by rw [hM, hN]; exact Scheme.Modules.Hom.app_smul _ _ _)

/-- The classes of the germs at `Z` in the stalk cokernels of `α`, as a `κ`-linear map, when
taking germs is `κ`-linear. -/
noncomputable def germCokerₗ {X : Scheme.{u}} {κ : Type u} [Field κ] {Na Nb : X.Modules}
    [Module κ Γ(Nb, ⊤)] (α : Na ⟶ Nb) (Z : Finset X) [∀ y : X, Algebra κ (X.presheaf.stalk y)]
    [∀ y : X, Module κ (stalkCoker α y)]
    [∀ y : X, IsScalarTower κ (X.presheaf.stalk y) (stalkCoker α y)]
    (hgerm : ∀ (c : κ) (s : Γ(Nb, ⊤)) (y : X), (Nb.presheaf.Γgerm y).hom (c • s) =
      algebraMap κ (X.presheaf.stalk y) c • (Nb.presheaf.Γgerm y).hom s) :
    Γ(Nb, ⊤) →ₗ[κ] (∀ y : Z, stalkCoker α y) :=
  { germCoker α Z with
    map_smul' := fun c s => by
      funext y
      change (Submodule.Quotient.mk ((Nb.presheaf.Γgerm y).hom (c • s)) : stalkCoker α y) =
        c • (Submodule.Quotient.mk ((Nb.presheaf.Γgerm y).hom s) : stalkCoker α y)
      rw [hgerm, Submodule.Quotient.mk_smul, algebraMap_smul] }

/-- The matrix of a morphism of modules injective on stalks, in bases of global sections over
`κ`, is injective. -/
theorem injective_mulVec_toMatrix_appTopₗ {X : Scheme.{u}} {κ : Type u} [Field κ]
    (ω : κ →+* Γ(X, ⊤)) {M N : X.Modules} [Module κ Γ(M, ⊤)] [Module κ Γ(N, ⊤)]
    (hM : ∀ (c : κ) (s : Γ(M, ⊤)), c • s = ω c • s) (hN : ∀ (c : κ) (s : Γ(N, ⊤)), c • s = ω c • s)
    {ra rb : ℕ} (βa : Module.Basis (Fin ra) κ Γ(M, ⊤)) (βb : Module.Basis (Fin rb) κ Γ(N, ⊤))
    (φ : M ⟶ N) (hi : ∀ y, Function.Injective (stalkLinearMap M N φ y)) :
    Function.Injective (LinearMap.toMatrix βa βb (appTopₗ ω hM hN φ)).mulVec := by
  intro u u' huu
  rw [toMatrix_mulVec_eq, toMatrix_mulVec_eq] at huu
  exact βa.equivFun.symm.injective
    (app_injective_of_stalkLinearMap_injective φ ⊤ (fun y _ => hi y) (βb.equivFun.injective huu))

/-- **The kernel of the cokernel classes.** If `α` is injective on stalks and surjective off `Z`,
the coordinate vectors whose section has zero classes at `Z` are the image of the matrix of
`α`. -/
theorem ker_comp_equivFun_symm_eq_range_toMatrix {X : Scheme.{u}} {κ : Type u} [Field κ]
    (ω : κ →+* Γ(X, ⊤)) {Na Nb : X.Modules} [Module κ Γ(Na, ⊤)] [Module κ Γ(Nb, ⊤)] {ra rb : ℕ}
    (ha : ∀ (c : κ) (s : Γ(Na, ⊤)), c • s = ω c • s)
    (hb : ∀ (c : κ) (s : Γ(Nb, ⊤)), c • s = ω c • s)
    (βa : Module.Basis (Fin ra) κ Γ(Na, ⊤)) (βb : Module.Basis (Fin rb) κ Γ(Nb, ⊤))
    (α : Na ⟶ Nb) (Z : Finset X) [∀ y : X, Module κ (stalkCoker α y)]
    (G : Γ(Nb, ⊤) →ₗ[κ] (∀ y : Z, stalkCoker α y)) (hG : ∀ s, G s = germCoker α Z s)
    (hi : ∀ y, Function.Injective (stalkLinearMap Na Nb α y))
    (hs : ∀ y, y ∉ Z → Function.Surjective (stalkLinearMap Na Nb α y)) :
    LinearMap.ker (G ∘ₗ βb.equivFun.symm.toLinearMap) =
      LinearMap.range (LinearMap.toMatrix βa βb (appTopₗ ω ha hb α)).mulVecLin := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe, hG,
    germCoker_eq_zero_iff α Z hi hs, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨βa.equivFun w, ?_⟩
    rw [Matrix.mulVecLin_apply, toMatrix_mulVec_eq, LinearEquiv.symm_apply_apply]
    show βb.equivFun (α.app ⊤ w) = v
    rw [hw, LinearEquiv.apply_symm_apply]
  · rintro ⟨u, rfl⟩
    refine ⟨βa.equivFun.symm u, ?_⟩
    rw [Matrix.mulVecLin_apply, toMatrix_mulVec_eq, LinearEquiv.symm_apply_apply]
    rfl

/-- **The cokernel classes are surjective** by counting dimensions: if `α` is injective on stalks
and surjective off `Z`, the ranks differ by `d`, and the stalk cokernels at `Z`, of finite length
over stalks with residue field spanned by `κ`, have lengths adding up to `d`. -/
theorem surjective_comp_equivFun_symm_of_sum_length {X : Scheme.{u}} {κ : Type u} [Field κ]
    (ω : κ →+* Γ(X, ⊤)) {Na Nb : X.Modules} [Module κ Γ(Na, ⊤)] [Module κ Γ(Nb, ⊤)]
    {ra rb d : ℕ} (ha : ∀ (c : κ) (s : Γ(Na, ⊤)), c • s = ω c • s)
    (hb : ∀ (c : κ) (s : Γ(Nb, ⊤)), c • s = ω c • s)
    (βa : Module.Basis (Fin ra) κ Γ(Na, ⊤)) (βb : Module.Basis (Fin rb) κ Γ(Nb, ⊤))
    (α : Na ⟶ Nb) (Z : Finset X) [∀ y : X, Algebra κ (X.presheaf.stalk y)]
    [∀ y : X, Module κ (stalkCoker α y)]
    [∀ y : X, IsScalarTower κ (X.presheaf.stalk y) (stalkCoker α y)]
    (G : Γ(Nb, ⊤) →ₗ[κ] (∀ y : Z, stalkCoker α y)) (hG : ∀ s, G s = germCoker α Z s)
    (hi : ∀ y, Function.Injective (stalkLinearMap Na Nb α y))
    (hs : ∀ y, y ∉ Z → Function.Surjective (stalkLinearMap Na Nb α y)) (hr : rb = ra + d)
    (hres : ∀ y ∈ Z, ResidueIsBase κ (X.presheaf.stalk y))
    (hfl : ∀ y ∈ Z, IsArtinian (X.presheaf.stalk y) (stalkCoker α y) ∧
      IsNoetherian (X.presheaf.stalk y) (stalkCoker α y))
    (hd : ∑ y ∈ Z, (Module.length (X.presheaf.stalk y) (stalkCoker α y)).toNat = d) :
    Function.Surjective (G ∘ₗ βb.equivFun.symm.toLinearMap) := by
  haveI : ∀ y : Z, FiniteDimensional κ (stalkCoker α y) := fun y => by
    obtain ⟨h1, h2⟩ := hfl y y.2
    exact finiteDimensional_of_residueIsBase (hres y y.2)
  have hinjM : Function.Injective (LinearMap.toMatrix βa βb (appTopₗ ω ha hb α)).mulVecLin :=
    injective_mulVec_toMatrix_appTopₗ ω ha hb βa βb α hi
  have hrange : Module.finrank κ (LinearMap.range (G ∘ₗ βb.equivFun.symm.toLinearMap)) = d := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (G ∘ₗ βb.equivFun.symm.toLinearMap)
    rw [ker_comp_equivFun_symm_eq_range_toMatrix ω ha hb βa βb α Z G hG hi hs,
      LinearMap.finrank_range_of_inj hinjM,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Fintype.card_fin] at h1
    omega
  have htot : Module.finrank κ (∀ y : Z, stalkCoker α y) = d := by
    rw [Module.finrank_pi_fintype, ← hd, ← Finset.sum_coe_sort Z]
    refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨h1, h2⟩ := hfl y y.2
    exact finrank_eq_length_toNat_of_residueIsBase (hres y y.2)
  rw [← LinearMap.range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (hrange.trans htot.symm)

/-- **The determinant of the multiplications on the stalk cokernels.** If `fᵢ(y)` has residue
`λᵢ(y)` at each `y ∈ Z`, multiplication by `∑ᵢ bᵢ fᵢ(y)` on the stalk cokernels at `Z` has
determinant `∏_{y ∈ Z} (∑ᵢ bᵢ λᵢ(y)) ^ len(y)`. -/
theorem eval_prod_eq_det_pi_lsmul {X : Scheme.{u}} {κ : Type u} [Field κ]
    [∀ y : X, Algebra κ (X.presheaf.stalk y)] {Na Nb : X.Modules} (α : Na ⟶ Nb)
    [∀ y : X, Module κ (stalkCoker α y)]
    [∀ y : X, IsScalarTower κ (X.presheaf.stalk y) (stalkCoker α y)] (Z : Finset X)
    {σv : Type*} [Fintype σv] (f : σv → ∀ y : X, X.presheaf.stalk y) (lam : ∀ y : X, σv → κ)
    (hlam : ∀ y ∈ Z, ∀ i, f i y - algebraMap κ (X.presheaf.stalk y) (lam y i) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk y))
    (hres : ∀ y ∈ Z, ResidueIsBase κ (X.presheaf.stalk y))
    (hfl : ∀ y ∈ Z, IsArtinian (X.presheaf.stalk y) (stalkCoker α y) ∧
      IsNoetherian (X.presheaf.stalk y) (stalkCoker α y)) (b : σv → κ) :
    eval b (∏ y ∈ Z, (∑ i, C (lam y i) * MvPolynomial.X i) ^
      (Module.length (X.presheaf.stalk y) (stalkCoker α y)).toNat) =
      LinearMap.det (LinearMap.pi fun y : Z =>
        ((LinearMap.lsmul (X.presheaf.stalk y) (stalkCoker α y))
          (∑ i, algebraMap κ (X.presheaf.stalk y) (b i) * f i y)).restrictScalars κ ∘ₗ
          LinearMap.proj y) := by
  classical
  haveI : ∀ y : Z, FiniteDimensional κ (stalkCoker α y) := fun y => by
    obtain ⟨h1, h2⟩ := hfl y y.2
    exact finiteDimensional_of_residueIsBase (hres y y.2)
  rw [det_pi_comp_proj, map_prod, ← Finset.prod_coe_sort Z]
  refine Finset.prod_congr rfl fun y _ => ?_
  obtain ⟨h1, h2⟩ := hfl y y.2
  have hc : ∑ i, algebraMap κ (X.presheaf.stalk y) (b i) * f i y -
      algebraMap κ (X.presheaf.stalk y) (∑ i, b i * lam y i) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
    have : ∑ i, algebraMap κ (X.presheaf.stalk y) (b i) * f i y -
        algebraMap κ (X.presheaf.stalk y) (∑ i, b i * lam y i) =
        ∑ i, algebraMap κ (X.presheaf.stalk y) (b i) *
          (f i y - algebraMap κ (X.presheaf.stalk y) (lam y i)) := by
      simp only [map_sum, map_mul, mul_sub, Finset.sum_sub_distrib]
    rw [this]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hlam y y.2 i)
  rw [det_lsmul_eq_pow_of_residueIsBase (hres y y.2) hc,
    finrank_eq_length_toNat_of_residueIsBase (hres y y.2) (M := stalkCoker α y), map_pow,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, eval_C, eval_X, mul_comm]

/-- **The cokernel data from the stalks.** On a scheme `X` with `ω : κ → Γ(X, ⊤)`, let
`α₁ : N₂ ⟶ N₁`, `α₀ : N₁ ⟶ N₀` be injective on stalks and bijective off a finite set `Z`, at
whose points they are, up to isomorphisms `τ` commuting with them, multiplications. If the
coordinate morphisms `ξ i` are multiples `fᵢ(y) • τ₁ y` at `y ∈ Z`, the stalk cokernels have finite
length, the residue fields at `Z` are spanned by `κ`, and the cokernel lengths add up to
`rank V₁ - rank V₂ = rank V₀ - rank V₁`, then the Koszul data have cokernel determinant
`∏_{y ∈ Z} (∑ᵢ λᵢ(y) Xᵢ) ^ len(y)`, with `λᵢ(y)` a residue of `fᵢ(y)`. -/
theorem hasCokerDet_of_stalks {X : Scheme.{u}} {κ : Type u} [Field κ]
    (ω : κ →+* Γ(X, ⊤)) {N₂ N₁ N₀ : X.Modules} [Module κ Γ(N₂, ⊤)] [Module κ Γ(N₁, ⊤)]
    [Module κ Γ(N₀, ⊤)] (hs₂ : ∀ (c : κ) (s : Γ(N₂, ⊤)), c • s = ω c • s)
    (hs₁ : ∀ (c : κ) (s : Γ(N₁, ⊤)), c • s = ω c • s)
    (hs₀ : ∀ (c : κ) (s : Γ(N₀, ⊤)), c • s = ω c • s)
    {r₂ r₁ r₀ d : ℕ} (h₁ : r₁ = r₂ + d) (h₀ : r₀ = r₁ + d)
    (β₂ : Module.Basis (Fin r₂) κ Γ(N₂, ⊤)) (β₁ : Module.Basis (Fin r₁) κ Γ(N₁, ⊤))
    (β₀ : Module.Basis (Fin r₀) κ Γ(N₀, ⊤))
    {σv : Type*} [Fintype σv] (ξ : σv → (N₁ ⟶ N₀)) (α₁ : N₂ ⟶ N₁) (α₀ : N₁ ⟶ N₀)
    (Z : Finset X)
    (hinj₁ : ∀ y, Function.Injective (stalkLinearMap N₂ N₁ α₁ y))
    (hsurj₁ : ∀ y, y ∉ Z → Function.Surjective (stalkLinearMap N₂ N₁ α₁ y))
    (hinj₀ : ∀ y, Function.Injective (stalkLinearMap N₁ N₀ α₀ y))
    (hsurj₀ : ∀ y, y ∉ Z → Function.Surjective (stalkLinearMap N₁ N₀ α₀ y))
    (τ₂ : X → (N₂ ⟶ N₁)) (τ₁ : X → (N₁ ⟶ N₀))
    (hcomm : ∀ y ∈ Z, α₁ ≫ τ₁ y = τ₂ y ≫ α₀)
    (hτ₂ : ∀ y ∈ Z, Function.Bijective (stalkLinearMap N₂ N₁ (τ₂ y) y))
    (hτ₁ : ∀ y ∈ Z, Function.Bijective (stalkLinearMap N₁ N₀ (τ₁ y) y))
    (f : σv → ∀ y : X, X.presheaf.stalk y)
    (hf : ∀ i, ∀ y ∈ Z, stalkLinearMap N₁ N₀ (ξ i) y = f i y • stalkLinearMap N₁ N₀ (τ₁ y) y)
    (hres : ∀ y ∈ Z, letI := stalkAlgebra ω y; ResidueIsBase κ (X.presheaf.stalk y))
    (hfl₁ : ∀ y ∈ Z, IsArtinian (X.presheaf.stalk y) (stalkCoker α₁ y) ∧
      IsNoetherian (X.presheaf.stalk y) (stalkCoker α₁ y))
    (hfl₀ : ∀ y ∈ Z, IsArtinian (X.presheaf.stalk y) (stalkCoker α₀ y) ∧
      IsNoetherian (X.presheaf.stalk y) (stalkCoker α₀ y))
    (hdim₁ : ∑ y ∈ Z, (Module.length (X.presheaf.stalk y) (stalkCoker α₁ y)).toNat = d)
    (hdim₀ : ∑ y ∈ Z, (Module.length (X.presheaf.stalk y) (stalkCoker α₀ y)).toNat = d) :
    ∃ lam : ∀ y : X, σv → κ, (∀ y ∈ Z, ∀ i, letI := stalkAlgebra ω y;
        f i y - algebraMap κ (X.presheaf.stalk y) (lam y i) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk y)) ∧
      HasCokerDet (fun i => LinearMap.toMatrix β₁ β₀ (appTopₗ ω hs₁ hs₀ (ξ i)))
        (LinearMap.toMatrix β₂ β₁ (appTopₗ ω hs₂ hs₁ α₁))
        (LinearMap.toMatrix β₁ β₀ (appTopₗ ω hs₁ hs₀ α₀))
        (∏ y ∈ Z, (∑ i, C (lam y i) * MvPolynomial.X i) ^
          (Module.length (X.presheaf.stalk y) (stalkCoker α₁ y)).toNat) := by
  classical
  letI : ∀ y : X, Algebra κ (X.presheaf.stalk y) := fun y => stalkAlgebra ω y
  letI : ∀ {Na Nb : X.Modules} (α : Na ⟶ Nb) (y : X), Module κ (stalkCoker α y) := fun _ y =>
    Module.compHom _ (algebraMap κ (X.presheaf.stalk y))
  haveI : ∀ {Na Nb : X.Modules} (α : Na ⟶ Nb) (y : X),
      IsScalarTower κ (X.presheaf.stalk y) (stalkCoker α y) := fun _ _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hres' : ∀ y ∈ Z, ResidueIsBase κ (X.presheaf.stalk y) := hres
  choose! lam hlam using fun y (hy : y ∈ Z) (i : σv) => hres' y hy (f i y)
  refine ⟨lam, hlam, ?_⟩
  -- the germ maps, linear over `κ`
  have hgerm₁ : ∀ (c : κ) (s : Γ(N₁, ⊤)) (y : X), (N₁.presheaf.Γgerm y).hom (c • s) =
      algebraMap κ (X.presheaf.stalk y) c • (N₁.presheaf.Γgerm y).hom s := by
    intro c s y
    rw [hs₁]
    exact PresheafOfModules.germ_smul (M := N₁.val) y ⊤ trivial (ω c) s
  have hgerm₀ : ∀ (c : κ) (s : Γ(N₀, ⊤)) (y : X), (N₀.presheaf.Γgerm y).hom (c • s) =
      algebraMap κ (X.presheaf.stalk y) c • (N₀.presheaf.Γgerm y).hom s := by
    intro c s y
    rw [hs₀]
    exact PresheafOfModules.germ_smul (M := N₀.val) y ⊤ trivial (ω c) s
  let G₁ := germCokerₗ α₁ Z hgerm₁
  let G₀ := germCokerₗ α₀ Z hgerm₀
  have hG₁ : ∀ s y, G₁ s y = Submodule.Quotient.mk ((N₁.presheaf.Γgerm y).hom s) := fun _ _ => rfl
  have hG₀ : ∀ s y, G₀ s y = Submodule.Quotient.mk ((N₀.presheaf.Γgerm y).hom s) := fun _ _ => rfl
  let E₁ := G₁ ∘ₗ β₁.equivFun.symm.toLinearMap
  let E₀ := G₀ ∘ₗ β₀.equivFun.symm.toLinearMap
  have hk₁ := ker_comp_equivFun_symm_eq_range_toMatrix ω hs₂ hs₁ β₂ β₁ α₁ Z G₁ (fun _ => rfl)
    hinj₁ hsurj₁
  have hk₀ := ker_comp_equivFun_symm_eq_range_toMatrix ω hs₁ hs₀ β₁ β₀ α₀ Z G₀ (fun _ => rfl)
    hinj₀ hsurj₀
  have hE₁ := surjective_comp_equivFun_symm_of_sum_length ω hs₂ hs₁ β₂ β₁ α₁ Z G₁ (fun _ => rfl)
    hinj₁ hsurj₁ h₁ hres' hfl₁ hdim₁
  have hE₀ := surjective_comp_equivFun_symm_of_sum_length ω hs₁ hs₀ β₁ β₀ α₀ Z G₀ (fun _ => rfl)
    hinj₀ hsurj₀ h₀ hres' hfl₀ hdim₀
  -- the comparison `P` and the endomorphisms `Φ b`
  let P : (∀ y : Z, stalkCoker α₁ y) ≃ₗ[κ] (∀ y : Z, stalkCoker α₀ y) :=
    LinearEquiv.piCongrRight fun y : Z => (stalkCokerEquiv α₁ α₀ (τ₂ y) (τ₁ y) y (hcomm y y.2)
      (hτ₂ y y.2) (hτ₁ y y.2)).restrictScalars κ
  let g : (σv → κ) → ∀ y : X, X.presheaf.stalk y := fun b y =>
    ∑ i, algebraMap κ (X.presheaf.stalk y) (b i) * f i y
  let Φ : (σv → κ) → (∀ y : Z, stalkCoker α₁ y) →ₗ[κ] (∀ y : Z, stalkCoker α₁ y) := fun b =>
    LinearMap.pi fun y : Z =>
      ((LinearMap.lsmul (X.presheaf.stalk y) (stalkCoker α₁ y)) (g b y)).restrictScalars κ ∘ₗ
        LinearMap.proj y
  have hΦ : ∀ b v, E₀ (Matrix.mulVec (∑ i, b i • LinearMap.toMatrix β₁ β₀
      (appTopₗ ω hs₁ hs₀ (ξ i))) v) = P (Φ b (E₁ v)) := by
    intro b v
    have hsum : ∑ i, b i • LinearMap.toMatrix β₁ β₀ (appTopₗ ω hs₁ hs₀ (ξ i)) =
        LinearMap.toMatrix β₁ β₀ (∑ i, b i • appTopₗ ω hs₁ hs₀ (ξ i)) := by
      simp only [map_sum, map_smul]
    rw [hsum, toMatrix_mulVec_eq]
    set s := β₁.equivFun.symm v
    show G₀ (β₀.equivFun.symm (β₀.equivFun _)) = P (Φ b (G₁ s))
    rw [LinearEquiv.symm_apply_apply]
    funext y
    rw [hG₀]
    show _ = stalkCokerEquiv α₁ α₀ (τ₂ y) (τ₁ y) y (hcomm y y.2) (hτ₂ y y.2) (hτ₁ y y.2)
      (g b y • G₁ s y)
    rw [hG₁, ← Submodule.Quotient.mk_smul, stalkCokerEquiv_mk]
    congr 1
    have hterm : ∀ i, (N₀.presheaf.Γgerm (y : X)).hom ((b i • appTopₗ ω hs₁ hs₀ (ξ i)) s) =
        (algebraMap κ (X.presheaf.stalk (y : X)) (b i) * f i y) •
          stalkLinearMap N₁ N₀ (τ₁ y) y ((N₁.presheaf.Γgerm (y : X)).hom s) := by
      intro i
      have hstalk : (N₀.presheaf.Γgerm (y : X)).hom ((ξ i).app ⊤ s) =
          stalkLinearMap N₁ N₀ (ξ i) y ((N₁.presheaf.Γgerm (y : X)).hom s) :=
        (stalkLinearMap_germ N₁ N₀ (ξ i) ⊤ y trivial s).symm
      rw [LinearMap.smul_apply, hgerm₀, mul_smul]
      congr 1
      exact hstalk.trans (by rw [hf i y y.2, LinearMap.smul_apply])
    rw [LinearMap.sum_apply, map_sum]
    simp only [hterm]
    rw [← Finset.sum_smul, map_smul]
  have hQ : ∀ b : σv → κ, eval b (∏ y ∈ Z, (∑ i, C (lam y i) * MvPolynomial.X i) ^
      (Module.length (X.presheaf.stalk y) (stalkCoker α₁ y)).toNat) = LinearMap.det (Φ b) :=
    eval_prod_eq_det_pi_lsmul α₁ Z f lam hlam hres' hfl₁
  exact ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance,
    E₁, E₀, P, Φ, hE₁, hE₀, hk₁, hk₀, hΦ, hQ⟩

end CokerDet

section RestrictAt

/-- Evaluating a polynomial with coefficients sent through `C ∘ f` and variables to `X` is
`MvPolynomial.map f`. -/
theorem eval₂_C_comp_X_eq_map {R R' σ' : Type*} [CommSemiring R] [CommSemiring R'] (f : R →+* R')
    (p : MvPolynomial σ' R) : eval₂ ((C : R' →+* _).comp f) X p = MvPolynomial.map f p := by
  induction p using MvPolynomial.induction_on <;> simp_all

/-- The specialization `R[u, v] → κ(x)[v]` at the point `x` and the first hyperplane `u = a`. -/
noncomputable def LocalFreeData.restrictAt (D : LocalFreeData g sS π q d s) (x : D.U)
    (a : Fin (N + 1) → k) : D.Pol →+* MvPolynomial (Fin (N + 1)) (D.U.residueField x) :=
  eval₂Hom ((C : D.U.residueField x →+* _).comp (D.U.Γevaluation x).hom)
    (Sum.elim (fun j => C (kEval (D.ι ≫ sS) x (a j))) X)

/-- At a closed point `x`, the specialization `D.restrictAt x a` is surjective. -/
theorem LocalFreeData.restrictAt_surjective (D : LocalFreeData g sS π q d s) (x : D.U)
    (hx : IsClosed ({x} : Set D.U)) (a : Fin (N + 1) → k) :
    Function.Surjective (D.restrictAt x a) := by
  intro p
  obtain ⟨p', rfl⟩ := MvPolynomial.map_surjective _ (Γevaluation_surjective (D.ι ≫ sS) x hx) p
  refine ⟨rename Sum.inr p', ?_⟩
  simp only [LocalFreeData.restrictAt, coe_eval₂Hom, eval₂_rename, Sum.elim_comp_inr]
  exact eval₂_C_comp_X_eq_map _ p'

/-- If `P` specializes at `x` to the image of a polynomial `F'` over `k`, then
`D.restrictAt x a P` is the image of the restriction `restrictU a F'` of `F'` to `u = a`. -/
theorem LocalFreeData.restrictAt_eq (D : LocalFreeData g sS π q d s) (x : D.U)
    (a : Fin (N + 1) → k) (P : D.Pol) (F' : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
    (hPF : MvPolynomial.map (kEval (D.ι ≫ sS) x) F' = D.specHom x P) :
    D.restrictAt x a P = MvPolynomial.map (kEval (D.ι ≫ sS) x) (restrictU a F') := by
  have h1 : D.restrictAt x a P = eval₂ C (Sum.elim (fun j => C (kEval (D.ι ≫ sS) x (a j))) X)
      (D.specHom x P) := by
    simp only [LocalFreeData.restrictAt, LocalFreeData.specHom, coe_eval₂Hom, eval₂_map]
  rw [h1, ← hPF, eval₂_map, restrictU, aeval_def, eval₂_comp_left]
  congr 1
  · ext r; simp
  · funext i; rcases i with i | i <;> simp

/-- The image of the matrix `D.A` under `D.restrictAt x a`: the rows `-∑ i, X i • D.X₁ i`
stacked on the constant rows `∑ j, a j • D.X₁ j`, with the matrices `D.X₁` read in the residue
field at `x`. -/
theorem LocalFreeData.A_map_restrictAt (D : LocalFreeData g sS π q d s) (x : D.U)
    (a : Fin (N + 1) → k) :
    D.A.map (D.restrictAt x a) = Matrix.fromRows
      (-(∑ i, (X i : MvPolynomial (Fin (N + 1)) (D.U.residueField x)) •
        ((D.X₁ i).map (D.U.Γevaluation x).hom).map (C (σ := Fin (N + 1)))))
      ((∑ j, kEval (D.ι ≫ sS) x (a j) • (D.X₁ j).map (D.U.Γevaluation x).hom).map
        (C (σ := Fin (N + 1)))) := by
  rw [D.A_map_ring]
  congr 1
  · congr 1
    ext i l
    simp [LocalFreeData.ellV₁, LocalFreeData.restrictAt, Matrix.sum_apply]
  · ext i l
    simp [LocalFreeData.ellU₁, LocalFreeData.restrictAt, Matrix.sum_apply]

/-- The image of the matrix `D.B` under `D.restrictAt x a`: the constant columns
`∑ j, a j • D.X₀ j` followed by the columns `∑ i, X i • D.X₀ i`, with the matrices `D.X₀` read
in the residue field at `x`. -/
theorem LocalFreeData.B_map_restrictAt (D : LocalFreeData g sS π q d s) (x : D.U)
    (a : Fin (N + 1) → k) :
    D.B.map (D.restrictAt x a) = Matrix.fromCols
      ((∑ j, kEval (D.ι ≫ sS) x (a j) • (D.X₀ j).map (D.U.Γevaluation x).hom).map
        (C (σ := Fin (N + 1))))
      (∑ i, (X i : MvPolynomial (Fin (N + 1)) (D.U.residueField x)) •
        ((D.X₀ i).map (D.U.Γevaluation x).hom).map (C (σ := Fin (N + 1)))) := by
  rw [D.B_map_ring]
  congr 1
  · ext i l
    simp [LocalFreeData.ellU₀, LocalFreeData.restrictAt, Matrix.sum_apply]
  · ext i l
    simp [LocalFreeData.ellV₀, LocalFreeData.restrictAt, Matrix.sum_apply]

/-- Applying a ring homomorphism `f` to the entries of `∑ j, c j • M j` gives
`∑ j, f (c j) • (M j).map f`. -/
theorem map_sum_smul {R R' : Type*} [Semiring R] [Semiring R'] (f : R →+* R')
    {m n ι : Type*} [Fintype ι] (c : ι → R) (M : ι → Matrix m n R) :
    (∑ j, c j • M j).map f = ∑ j, f (c j) • (M j).map f := by
  ext i l; simp [Matrix.sum_apply]

/-- **The fibre polynomial restricted to a first hyperplane.** Let the fibre matrices at `x` be
the images, under a field homomorphism `ε : κ' → κ(x)`, of matrices `Y₁ j`, `Y₀ j` over `κ'`. If
the cokernels of `ℓ_a` on them are identified with `κ'`-spaces `M₁ ≃ M₀` on which `ℓ_b` acts with
determinant `Q(b)`, then the restriction of the fibre polynomial to `u = a` is a nonzero constant
times the image of `Q`. -/
theorem LocalFreeData.exists_restrictU_eq_C_mul (D : LocalFreeData g sS π q d s)
    (x : D.U) (hx : IsClosed ({x} : Set D.U)) {F' : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    (hF' : IsFibrePoly D x F') (a : Fin (N + 1) → k)
    {κ' : Type*} [Field κ'] [Infinite κ'] (ε : κ' →+* D.U.residueField x)
    (Y₁ : Fin (N + 1) → Matrix (Fin D.r₁) (Fin D.r₂) κ')
    (Y₀ : Fin (N + 1) → Matrix (Fin D.r₀) (Fin D.r₁) κ')
    (hY₁ : ∀ j, (D.X₁ j).map (D.U.Γevaluation x).hom = (Y₁ j).map ε)
    (hY₀ : ∀ j, (D.X₀ j).map (D.U.Γevaluation x).hom = (Y₀ j).map ε)
    (a' : Fin (N + 1) → κ') (ha' : ∀ j, ε (a' j) = kEval (D.ι ≫ sS) x (a j))
    (hLa : Function.Injective (∑ j, a' j • Y₁ j).mulVec)
    (hL'a : Function.Injective (∑ j, a' j • Y₀ j).mulVec)
    (Q : MvPolynomial (Fin (N + 1)) κ')
    (hQ : HasCokerDet Y₀ (∑ j, a' j • Y₁ j) (∑ j, a' j • Y₀ j) Q)
    (hQ0 : Q ≠ 0) :
    ∃ c : κ', c ≠ 0 ∧
      MvPolynomial.map (kEval (D.ι ≫ sS) x) (restrictU a F') = C (ε c) * MvPolynomial.map ε Q := by
  classical
  obtain ⟨P', hP', hPF⟩ := hF'
  have hinj : ∀ {m n : ℕ}, Function.Injective (fun M : Matrix (Fin m) (Fin n) κ' => M.map ε) :=
    fun h => Matrix.map_injective ε.injective h
  have hcomm : ∀ i, (∑ j, a' j • Y₀ j) * Y₁ i = Y₀ i * (∑ j, a' j • Y₁ j) := by
    intro i
    apply hinj
    simp only [Matrix.map_mul, map_sum_smul, ← hY₁, ← hY₀, ha']
    rw [Matrix.sum_mul, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, D.comm j i]
  obtain ⟨M₁, M₀, _, _, _, _, E₁, E₀, P, Φ, hE₁, hE₀, hk₁, hk₀, hΦ, hQ⟩ := hQ
  obtain ⟨hsplit', c, hc, hdet'⟩ := isSplitExact_and_exists_complexDet_eq_C_mul D.rank₁ D.rank₀
    D.e Y₁ Y₀ _ _ hcomm hLa hL'a E₁ E₀ hE₁ hE₀ hk₁ hk₀ P Φ hΦ Q hQ hQ0
  set f : MvPolynomial (Fin (N + 1)) κ' →+* MvPolynomial (Fin (N + 1)) (D.U.residueField x) :=
    MvPolynomial.map ε with hf
  have hfinj : Function.Injective ((algebraMap _
      (FractionRing (MvPolynomial (Fin (N + 1)) (D.U.residueField x)))).comp f) :=
    (IsFractionRing.injective _ _).comp (MvPolynomial.map_injective ε ε.injective)
  let φ : FractionRing (MvPolynomial (Fin (N + 1)) κ') →+*
      FractionRing (MvPolynomial (Fin (N + 1)) (D.U.residueField x)) := IsFractionRing.lift hfinj
  have hφ : φ.comp (algebraMap _ _) = (algebraMap _ _).comp f := by
    ext z <;> simp [φ]
  have hY₁' : ∀ j i l, (D.U.Γevaluation x).hom (D.X₁ j i l) = ε (Y₁ j i l) := fun j i l =>
    congrFun (congrFun (hY₁ j) i) l
  have hY₀' : ∀ j i l, (D.U.Γevaluation x).hom (D.X₀ j i l) = ε (Y₀ j i l) := fun j i l =>
    congrFun (congrFun (hY₀ j) i) l
  set A' := Matrix.fromRows (-(∑ i, (X i : MvPolynomial (Fin (N + 1)) κ') • (Y₁ i).map
      (C (σ := Fin (N + 1))))) ((∑ j, a' j • Y₁ j).map (C (σ := Fin (N + 1)))) with hA'
  set B' := Matrix.fromCols ((∑ j, a' j • Y₀ j).map (C (σ := Fin (N + 1))))
      (∑ i, (X i : MvPolynomial (Fin (N + 1)) κ') • (Y₀ i).map (C (σ := Fin (N + 1)))) with hB'
  have hBA' : B' * A' = 0 := by
    rw [hA', hB', Matrix.fromCols_mul_fromRows, Matrix.mul_neg, neg_add_eq_zero]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.map_mul, hcomm]
  obtain ⟨hsplit, hmap⟩ := MMP.Chow.complexDet_map f φ hφ hBA' hsplit'
  have hA : A'.map f = D.A.map (D.restrictAt x a) := by
    rw [D.A_map_restrictAt]
    ext (i | i) l <;> simp [hA', Matrix.sum_apply, hY₁', ha', hf]
  have hB : B'.map f = D.B.map (D.restrictAt x a) := by
    rw [D.B_map_restrictAt]
    ext i (l | l) <;> simp [hB', Matrix.sum_apply, hY₀', ha', hf]
  rw [hA, hB] at hsplit hmap
  have key := specialize_complexDet (K := FractionRing D.Pol)
    (K' := FractionRing (MvPolynomial (Fin (N + 1)) (D.U.residueField x))) (D.restrictAt x a)
    (D.restrictAt_surjective x hx a) hsplit D.B_mul_A P' hP'
  rw [hmap, hdet'] at key
  have h2 : φ (algebraMap _ _ (C c * Q)) = algebraMap _ _ (f (C c * Q)) :=
    RingHom.congr_fun hφ _
  rw [h2] at key
  refine ⟨c, hc, ?_⟩
  rw [← D.restrictAt_eq x a P' F' hPF]
  have := IsFractionRing.injective _ _ key
  rw [this, map_mul, hf, MvPolynomial.map_C]

end RestrictAt

section FibrePlumbing

/-- The structure map of the fibre over `t`, read through its residue field. -/
theorem baseRingHom_kEval {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (π : 𝒞 ⟶ S)
    (t : S) (c : k) :
    (Stacks.Cech.baseRingHom (π.fiberToSpecResidueField t) ⊤).hom (kEval sS t c) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (π.fiberι t ≫ π ≫ sS).appTop).hom c := by
  rw [fiber_structure_eq sS π t, Scheme.Hom.comp_appTop]
  have h1 := congrArg (fun φ => φ.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (kEval sS t)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  simp only [Stacks.Cech.baseRingHom, Stacks.Cech.globalRingHom, CommRingCat.hom_comp,
    RingHom.comp_apply, ← h1]
  rw [show (homOfLE (le_refl (⊤ : (π.fiber t).Opens))) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  refine Eq.trans ?_ (congrArg (fun z => (π.fiberToSpecResidueField t).appTop.hom z) h1)
  simp only [CommRingCat.hom_id, RingHom.id_comp, CommRingCat.hom_comp, RingHom.comp_apply]
  rfl

/-- The structure map at a point of an open, read in the residue field of the ambient scheme. -/
theorem residueFieldMap_kEval {S : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (W : S.Opens)
    (x : W.toScheme) (c : k) :
    (W.ι.residueFieldMap x).hom (kEval sS (W.ι x) c) = kEval (W.ι ≫ sS) x c := by
  have h := congrArg (fun φ => φ.hom (((Scheme.ΓSpecIso (.of k)).inv ≫ sS.appTop).hom c))
    (Scheme.Γevaluation_naturality W.ι x)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  simp only [kEval, MMP.Chow.structureAlgebra, RingHom.comp_apply]
  exact h

/-- **The residue fields of a closed fibre at its closed points are spanned by `κ(t)`.** -/
theorem residueIsBase_fibre {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (π : 𝒞 ⟶ S)
    (t : S) [LocallyOfFiniteType (π.fiberι t ≫ π ≫ sS)] (y : π.fiber t)
    (hy : IsClosed ({y} : Set (π.fiber t))) :
    letI : Algebra (S.residueField t) ((π.fiber t).presheaf.stalk y) :=
      stalkAlgebra (Stacks.Cech.baseRingHom (π.fiberToSpecResidueField t) ⊤).hom y
    ResidueIsBase (S.residueField t) ((π.fiber t).presheaf.stalk y) := by
  letI : Algebra (S.residueField t) ((π.fiber t).presheaf.stalk y) :=
    stalkAlgebra (Stacks.Cech.baseRingHom (π.fiberToSpecResidueField t) ⊤).hom y
  intro r
  obtain ⟨c₀, hc₀⟩ := (kEval_bijective (π.fiberι t ≫ π ≫ sS) y hy).2
    (IsLocalRing.residue _ r)
  refine ⟨kEval sS t c₀, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc₀]
  show _ = IsLocalRing.residue _ ((((π.fiber t).presheaf.Γgerm y).hom)
    ((Stacks.Cech.baseRingHom (π.fiberToSpecResidueField t) ⊤).hom (kEval sS t c₀)))
  rw [baseRingHom_kEval]
  rfl

end FibrePlumbing

section FibreStalkAux

/-- **Multiplication by proportional sections, after two pullbacks.** -/
theorem stalkLinearMap_pullback₂_coordMul_eq {X₁ X₂ X₃ : Scheme.{u}} (ρ₁ : X₁ ⟶ X₂)
    (ρ₂ : X₂ ⟶ X₃) (H A : X₃.Modules) [Stacks.Ample.IsInvertibleModule X₃ H]
    [Stacks.Ample.IsInvertibleModule X₃ A]
    [Stacks.Ample.IsInvertibleModule X₂ ((Scheme.Modules.pullback ρ₂).obj H)]
    [Stacks.Ample.IsInvertibleModule X₁
      ((Scheme.Modules.pullback ρ₁).obj ((Scheme.Modules.pullback ρ₂).obj H))]
    (n : ℕ) (m : ℤ) (σ τ : Γ(H, ⊤)) (y : X₁)
    (hτ : ρ₂ (ρ₁ y) ∈ Stacks.Ample.nonvanishingLocus H τ)
    (hτ' : ρ₁ y ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback ρ₂).obj H)
      (pullbackGlobalSections ρ₂ H τ))
    (hτ'' : y ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback ρ₁).obj ((Scheme.Modules.pullback ρ₂).obj H))
      (pullbackGlobalSections ρ₁ _ (pullbackGlobalSections ρ₂ H τ))) :
    stalkLinearMap _ _ ((Scheme.Modules.pullback ρ₁).map ((Scheme.Modules.pullback ρ₂).map
        (MMP.Chow.coordMul H A σ n m))) y =
      (Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus _ _ hτ'').coord
        ((((Scheme.Modules.pullback ρ₁).obj ((Scheme.Modules.pullback ρ₂).obj H)).presheaf.Γgerm
          y).hom (pullbackGlobalSections ρ₁ _ (pullbackGlobalSections ρ₂ H σ))) •
      stalkLinearMap _ _ ((Scheme.Modules.pullback ρ₁).map ((Scheme.Modules.pullback ρ₂).map
        (MMP.Chow.coordMul H A τ n m))) y := by
  have h3 := stalkLinearMap_coordMul_eq_coord_smul H A n m σ τ hτ
  have h2 := stalkLinearMap_pullback_map_eq_smul ρ₂ _ _ (ρ₁ y) _ h3
  have h1 := stalkLinearMap_pullback_map_eq_smul ρ₁ _ _ y _ h2
  rw [h1, coord_pullbackGlobalSections ρ₁ _ _ _ hτ' hτ'',
    coord_pullbackGlobalSections ρ₂ H σ τ hτ hτ']

/-- A nonzerodivisor of the local ring acts injectively on a stalk with a stalk basis. -/
theorem injective_smul_stalk_of_isStalkBasis {X : Scheme.{u}} {N : X.Modules} {y : X}
    {n : N.presheaf.stalk y} (hn : Stacks.Divisors.IsStalkBasis N y n) {r : X.presheaf.stalk y}
    (hr : r ∈ nonZeroDivisors (X.presheaf.stalk y)) :
    Function.Injective fun m : N.presheaf.stalk y => r • m := by
  intro m m' h
  obtain ⟨s, rfl⟩ := hn.surjective m
  obtain ⟨s', rfl⟩ := hn.surjective m'
  have h' : (r * s) • n = (r * s') • n := by rw [mul_smul, mul_smul]; exact h
  have := hn.injective h'
  have h0 : r * (s - s') = 0 := by rw [mul_sub, this, sub_self]
  rw [mul_comm] at h0
  have := (mem_nonZeroDivisors_iff.mp hr).2 _ h0
  show s • n = s' • n
  rw [sub_eq_zero.mp this]

/-- Modules of finite length are Artinian and Noetherian, across an isomorphism. -/
theorem isArtinian_and_isNoetherian_of_length_ne_top {R M M' : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M')
    (h : Module.length R M' ≠ ⊤) : IsArtinian R M ∧ IsNoetherian R M := by
  have h' : Module.length R M ≠ ⊤ := by rw [e.length_eq]; exact h
  have hf := Module.length_ne_top_iff.mp h'
  exact ⟨(isFiniteLength_iff_isNoetherian_isArtinian.mp hf).2,
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hf).1⟩

end FibreStalkAux

section FibreAssembly

attribute [local instance 10000] HasDerivedCategory.standard

/-- The coefficient of `Xⱼ` in the linear form `∑ i, lᵢ Xᵢ` is `lⱼ`. -/
theorem coeff_single_sum_C_mul_X {K : Type*} [CommSemiring K] {n : ℕ} (l : Fin n → K)
    (j : Fin n) :
    (∑ i, MvPolynomial.C (l i) * MvPolynomial.X i : MvPolynomial (Fin n) K).coeff
      (Finsupp.single j 1) = l j := by
  simp only [coeff_sum, coeff_C_mul, coeff_X', Finsupp.single_eq_single_iff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Ne.symm hb, hb]
  · simp

/-- The linear form with a nonzero coefficient vector has total degree one. -/
theorem totalDegree_sum_C_mul_X {K : Type*} [Field K] {n : ℕ} (l : Fin n → K)
    (hl : l ≠ 0) : (∑ i, MvPolynomial.C (l i) * MvPolynomial.X i :
      MvPolynomial (Fin n) K).totalDegree = 1 := by
  classical
  apply le_antisymm
  · refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · obtain ⟨j, hj⟩ : ∃ j, l j ≠ 0 := by
      by_contra h; push Not at h; exact hl (funext h)
    have := MvPolynomial.le_totalDegree (s := Finsupp.single j 1)
      (p := (∑ i, MvPolynomial.C (l i) * MvPolynomial.X i : MvPolynomial (Fin n) K))
      (by rwa [MvPolynomial.mem_support_iff, coeff_single_sum_C_mul_X])
    simpa using this

/-- Two linear forms over an algebraically closed field with the same zeros are proportional. -/
theorem exists_sum_C_mul_X_eq_C_mul {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (l l' : Fin n → K) (hl : l ≠ 0) (hl' : l' ≠ 0)
    (h : ∀ w : Fin n → K, ∑ i, l i * w i = 0 ↔ ∑ i, l' i * w i = 0) :
    ∃ c : Kˣ, (∑ i, MvPolynomial.C (l' i) * MvPolynomial.X i : MvPolynomial (Fin n) K) =
      MvPolynomial.C (c : K) * ∑ i, MvPolynomial.C (l i) * MvPolynomial.X i := by
  have hev : ∀ (m : Fin n → K) (w : Fin n → K),
      MvPolynomial.eval w (∑ i, MvPolynomial.C (m i) * MvPolynomial.X i) = ∑ i, m i * w i :=
    fun m w => by simp
  exact assoc_of_same_zeros (irreducible_of_totalDegree_eq_one (totalDegree_sum_C_mul_X l hl))
    (fun w => by rw [hev, hev]; exact h w)
    (irreducible_of_totalDegree_eq_one (totalDegree_sum_C_mul_X l' hl'))

/-- A linear form over `κ` with the zeros of the image of a linear form over `K` under a field
isomorphism `K ≃ κ` is a unit multiple of that image. -/
theorem exists_sum_C_mul_X_eq_C_mul_map {K κ : Type*} [Field K] [Field κ] [IsAlgClosed κ]
    {n : ℕ} (e : K →+* κ) (he : Function.Bijective e) (l : Fin n → κ) (p : Fin n → K)
    (hp : p ≠ 0) (hl : l ≠ 0) (h : ∀ b : Fin n → K, ∑ i, e (b i) * l i = 0 ↔ ∑ j, b j * p j = 0) :
    ∃ u : κˣ, (∑ i, MvPolynomial.C (l i) * MvPolynomial.X i : MvPolynomial (Fin n) κ) =
      MvPolynomial.C (u : κ) *
        MvPolynomial.map e (∑ j, MvPolynomial.C (p j) * MvPolynomial.X j) := by
  have hm : MvPolynomial.map e (∑ j, MvPolynomial.C (p j) * MvPolynomial.X j) =
      ∑ j, MvPolynomial.C (e (p j)) * MvPolynomial.X j := by
    simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [hm]
  refine exists_sum_C_mul_X_eq_C_mul _ _ (fun h0 => hp (funext fun j => he.1 ?_)) hl fun w => ?_
  · rw [Pi.zero_apply, map_zero]
    exact congrFun h0 j
  · let ee := RingEquiv.ofBijective e he
    obtain ⟨b, rfl⟩ : ∃ b : Fin n → K, w = fun i => e (b i) :=
      ⟨fun i => ee.symm (w i), funext fun i => (ee.apply_symm_apply (w i)).symm⟩
    have e1 : ∑ i, e (p i) * e (b i) = e (∑ j, b j * p j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_comm]
    rw [e1, map_eq_zero_iff _ he.1, ← h b]
    exact Iff.of_eq (congrArg (· = (0 : κ)) (Finset.sum_congr rfl fun i _ => mul_comm _ _))

/-- **Assembly of the restricted determinant.** If, after mapping to the residue field of the
point, the fibre polynomial is a nonzero constant times a product of unit multiples of the images
of the pointwise forms `P y` raised to the powers `len y`, then it is a nonzero constant times the
product of the `P y ^ len y`. -/
theorem exists_eq_C_mul_prod_of_map_eq {K κ κ' : Type*} [Field K] [Field κ] [Field κ']
    {σ ι : Type*} (e : K →+* κ) (e' : K →+* κ') (ε : κ →+* κ') (hk : ε.comp e = e')
    (hbx : Function.Bijective e') (s : Finset ι) (P : ι → MvPolynomial σ K) (len : ι → ℕ)
    (u : ι → κˣ) (F'' : MvPolynomial σ K) (c₀ : κ) (hc₀ : c₀ ≠ 0)
    (hres : MvPolynomial.map e' F'' = C (ε c₀) *
      MvPolynomial.map ε (∏ y ∈ s, (C ((u y : κˣ) : κ) * MvPolynomial.map e (P y)) ^ len y)) :
    ∃ c : K, c ≠ 0 ∧ F'' = C c * ∏ y ∈ s, P y ^ len y := by
  classical
  set P' := ∏ y ∈ s, P y ^ len y with hPdef
  set U := ∏ y ∈ s, ((u y : κˣ) : κ) ^ len y with hUdef
  have h2 : MvPolynomial.map ε (∏ y ∈ s, (C ((u y : κˣ) : κ) * MvPolynomial.map e (P y)) ^ len y) =
      C (ε U) * MvPolynomial.map e' P' := by
    rw [Finset.prod_congr rfl fun y _ => mul_pow _ _ _, Finset.prod_mul_distrib, map_mul]
    congr 1
    · simp only [hUdef, map_prod, map_pow, MvPolynomial.map_C]
    · simp only [hPdef, map_prod, map_pow, MvPolynomial.map_map, hk]
  have hres'' : MvPolynomial.map e' F'' = C (ε (c₀ * U)) * MvPolynomial.map e' P' := by
    rw [hres, h2, map_mul, MvPolynomial.C_mul, mul_assoc]
  let ex := RingEquiv.ofBijective e' hbx
  have hU0 : U ≠ 0 := Finset.prod_ne_zero_iff.2 fun y _ => pow_ne_zero _ (u y).ne_zero
  refine ⟨ex.symm (ε (c₀ * U)), ?_, ?_⟩
  · exact fun h0 => (map_ne_zero ε).2 (mul_ne_zero hc₀ hU0)
      (ex.symm.injective (h0.trans (map_zero _).symm))
  · apply MvPolynomial.map_injective _ hbx.1
    refine hres''.trans ?_
    refine Eq.trans ?_ (map_mul (MvPolynomial.map e') _ P').symm
    refine congrArg (· * MvPolynomial.map e' P') ?_
    exact (congrArg C (ex.apply_symm_apply (ε (c₀ * U)))).symm.trans
      (MvPolynomial.map_C (σ := σ) e' (ex.symm (ε (c₀ * U)))).symm

/-- **Linear factors at the points of the zero locus.** Over a field `κ` with a bijective
ring homomorphism `e : k →+* κ`, if the local coordinates of the linear forms on the stalks of
the points of `Z` are congruent modulo the maximal ideal to the constants `lam y`, then each
`∑ i, lam y i * Xᵢ` is a unit multiple of the image of the point form `ptForm (ψ y)`. -/
theorem exists_unit_sum_C_mul_X_eq_C_mul_map_ptForm {Xs : Scheme.{u}} {κ : Type u} [Field κ]
    [IsAlgClosed κ] (e : k →+* κ) (he : Function.Bijective e) (ω : κ →+* Γ(Xs, ⊤))
    (Z : Finset Xs) (ψ : Xs → AlgebraicGeometry.Proj (polyGrading k N))
    (hZcl : ∀ y ∈ Z, IsClosed ({ψ y} : Set (AlgebraicGeometry.Proj (polyGrading k N))))
    (lam : Xs → Fin (N + 1) → κ) (crl : (Fin (N + 1) → k) → ∀ y : Xs, Xs.presheaf.stalk y)
    (crc : Fin (N + 1) → ∀ y : Xs, Xs.presheaf.stalk y)
    (hcrl : ∀ (b : Fin (N + 1) → k) (y : Xs), crl b y =
      ∑ i, (Xs.presheaf.Γgerm y).hom (ω (e (b i))) * crc i y)
    (hunit : ∀ (b : Fin (N + 1) → k), ∀ y ∈ Z,
      IsUnit (crl b y) ↔ linForm b ∉ (ψ y).asHomogeneousIdeal)
    (hlam : ∀ y ∈ Z, ∀ i, letI := stalkAlgebra ω y;
      crc i y - algebraMap κ (Xs.presheaf.stalk y) (lam y i) ∈
        IsLocalRing.maximalIdeal (Xs.presheaf.stalk y))
    (hlin0 : ∀ y ∈ Z, (∑ i, C (lam y i) * MvPolynomial.X i :
      MvPolynomial (Fin (N + 1)) κ) ≠ 0) :
    ∀ y ∈ Z, ∃ u : κˣ,
      (∑ i, C (lam y i) * MvPolynomial.X i : MvPolynomial (Fin (N + 1)) κ) =
        C (u : κ) * MvPolynomial.map e (ptForm (ψ y)) := by
  classical
  letI : ∀ y : Xs, Algebra κ (Xs.presheaf.stalk y) := fun y => stalkAlgebra ω y
  have hmodLin : ∀ (b : Fin (N + 1) → k), ∀ y ∈ Z, crl b y -
      algebraMap κ _ (∑ i, e (b i) * lam y i) ∈ IsLocalRing.maximalIdeal (Xs.presheaf.stalk y) := by
    intro b y hy
    have e1 : crl b y - algebraMap κ _ (∑ i, e (b i) * lam y i) = ∑ i, algebraMap κ
          (Xs.presheaf.stalk y) (e (b i)) * (crc i y - algebraMap _ _ (lam y i)) := by
      rw [hcrl, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, mul_sub]
      rfl
    rw [e1]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hlam y hy i)
  have hzero : ∀ (b : Fin (N + 1) → k), ∀ y ∈ Z,
      ∑ i, e (b i) * lam y i = 0 ↔ ∑ j, b j * ptCoord (ψ y) j = 0 := by
    intro b y hy
    rw [← linForm_mem_closedPt_iff _ (hZcl y hy), ← not_iff_not, ← hunit b y hy]
    constructor
    · intro h0
      by_contra hu
      have h1 : crl b y ∈ IsLocalRing.maximalIdeal _ := hu
      have h2 := Ideal.sub_mem _ h1 (hmodLin b y hy)
      rw [sub_sub_cancel] at h2
      exact h2 ((isUnit_iff_ne_zero.2 h0).map _)
    · intro hu h0
      have h1 := hmodLin b y hy
      rw [h0, map_zero, sub_zero] at h1
      exact h1 hu
  intro y hy
  exact exists_sum_C_mul_X_eq_C_mul_map e he (lam y) _
    (ptCoord_spec (ψ y)).1
    (fun h => hlin0 y hy (by simp [h]))
    (fun b => hzero b y hy)

/-- **The coordinate of a hyperplane on a fibre.** On the fibre over `t`, the coordinate of the
section of a hyperplane `linSection g q b`, in the basis given by a coordinate section not
vanishing at `y`, is the combination of the coordinates of the coordinate sections with the
constants `b i` read in the residue field of `t`. -/
theorem fibre_coord_linSection {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    (hgY : g ≫ projToSpecCoeff k N = sY) (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    (W : S.Opens) (t : S) (ht : t ∈ W)
    [Stacks.Ample.IsInvertibleModule (π ⁻¹ᵁ W).toScheme
      ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj (hyperplaneBundle g q))]
    [Stacks.Ample.IsInvertibleModule (π.fiber t)
      ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj (hyperplaneBundle g q)))]
    (hidx : ∀ y : π.fiber t, y ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj (hyperplaneBundle g q)))
      (pullbackGlobalSections (fiberιOfMem π t ht) _
        (pullbackGlobalSections (π ⁻¹ᵁ W).ι (hyperplaneBundle g q)
          (coordSection g q (fibreIdx g π q t y)))))
    (b : Fin (N + 1) → k) (y : π.fiber t) :
    (Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus _ _
      (hidx y)).coord
      (((((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj (hyperplaneBundle g q))).presheaf.Γgerm y).hom
        (pullbackGlobalSections (fiberιOfMem π t ht) _
          (pullbackGlobalSections (π ⁻¹ᵁ W).ι (hyperplaneBundle g q) (linSection g q b))))) =
    ∑ i, ((π.fiber t).presheaf.Γgerm y).hom
        ((Stacks.Cech.baseRingHom (π.fiberToSpecResidueField t) ⊤).hom (kEval sS t (b i))) *
      (Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus _ _
        (hidx y)).coord
        (((((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj
          ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj (hyperplaneBundle g q))).presheaf.Γgerm y).hom
          (pullbackGlobalSections (fiberιOfMem π t ht) _
            (pullbackGlobalSections (π ⁻¹ᵁ W).ι (hyperplaneBundle g q)
              (coordSection g q i))))) := by
  classical
  set H := hyperplaneBundle g q
  set g' := fiberιOfMem π t ht
  set ι' := (π ⁻¹ᵁ W).ι
  set ω : S.residueField t →+* Γ(π.fiber t, ⊤) :=
    (Stacks.Cech.baseRingHom (π.fiberToSpecResidueField t) ⊤).hom with hω
  have hmor : g' ≫ ι' ≫ q ≫ g ≫ projToSpecCoeff k N = π.fiberι t ≫ π ≫ sS := by
    rw [← Category.assoc g' ι', fiberιOfMem_ι, hgY, ← hπq]
  have hconst : ∀ r : k, g'.appTop.hom (ι'.appTop.hom
      ((q ≫ g).appTop.hom (Stacks.ProjectiveSpace.Cohomology.coeffToGlobalSections k N r))) =
      ω (kEval sS t r) := by
    intro r
    have h := congrArg (fun φ => ((Scheme.ΓSpecIso (.of k)).inv ≫ Scheme.Hom.appTop φ).hom r) hmor
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [hω]
    refine Eq.trans ?_ (baseRingHom_kEval sS π t r).symm
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact h
  have hσlin : ∀ b : Fin (N + 1) → k,
      pullbackGlobalSections g' _ (pullbackGlobalSections ι' H (linSection g q b)) =
      ∑ i, ω (kEval sS t (b i)) •
        pullbackGlobalSections g' _ (pullbackGlobalSections ι' H (coordSection g q i)) := by
    intro b
    show (pullbackGlobalSections g' _).hom
      ((pullbackGlobalSections ι' H).hom (linSection g q b)) = _
    rw [linSection]
    erw [pullbackGlobalSections_sum, pullbackGlobalSections_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [pullbackGlobalSections_smul, pullbackGlobalSections_smul, hconst]
  rw [hσlin, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hg := PresheafOfModules.germ_smul (M := ((Scheme.Modules.pullback g').obj
    ((Scheme.Modules.pullback ι').obj H)).val) y ⊤ trivial (ω (kEval sS t (b i)))
    (pullbackGlobalSections g' _ (pullbackGlobalSections ι' H (coordSection g q i)))
  erw [hg, LinearEquiv.map_smul]
  rfl

set_option maxRecDepth 8000 in
/-- **The fibre polynomial on a regular hyperplane.** Restricted to `u = a`, the fibre polynomial
is a nonzero scalar times `∏_y ℓ_{ψ(y)} ^ len(𝒪_{X,y}/ℓ_a)`. -/
theorem exists_restrictU_eq_C_mul_finprod_ptForm {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k))
    (hS : Mori.IsNormalVariety k sS) (hY : IsProjectiveMorphism sY)
    (g : Y ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (hg : IsProjectiveMorphism g)
    (hgY : g ≫ projToSpecCoeff k N = sY)
    (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY)
    [IsClosedImmersion (pullback.lift π q hπq)] [IsProper π] [Flat π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1)
    (d : ℕ) {s : S} (F : KoszulFamily g π q d s) :
    let D := F.toLocalFreeData hS
    ∀ x : D.U, IsClosed ({x} : Set D.U) →
    ∀ F' : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k, IsFibrePoly D x F' →
    ∀ a : Fin (N + 1) → k, FibreRegular g π q (D.ι x) a →
      (∑ᶠ y : π.fiber (D.ι x), fibreLen g π q (D.ι x) a y) = d →
      ∃ c : k, c ≠ 0 ∧ restrictU a F' = MvPolynomial.C c *
        ∏ᶠ y : π.fiber (D.ι x), ptForm (fibrePsi g π q (D.ι x) y) ^ fibreLen g π q (D.ι x) a y := by
  intro D x hx F' hF' a hreg hsum
  classical
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set W := F.data.W
  set t : S := W.ι x
  have ht : t ∈ W := x.2
  have htc : IsClosed ({t} : Set S) :=
    isClosed_image_of_isClosed sS (D.ι ≫ sS) D.ι rfl x hx
  obtain ⟨-, hFprop, hdimF, -, -, -⟩ := fibre_facts sS sY hS hY g hg hgY π q hπq hdim t htc
  obtain ⟨hZfin, hZcl, hlen⟩ := fibreZero_facts sS sY hS hY g hg hgY π q hπq hdim t htc a hreg
  haveI := hFprop
  haveI : LocallyOfFiniteType (π.fiberι t ≫ π ≫ sS) := hFprop.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (π.fiber t) :=
    LocallyOfFiniteType.isLocallyNoetherian (π.fiberι t ≫ π ≫ sS)
  -- the fibre and the twists on it
  set H := hyperplaneBundle g q
  set g' := fiberιOfMem π t ht
  set ι' := (π ⁻¹ᵁ W).ι
  have hg'ι : ∀ y, ι' (g' y) = π.fiberι t y := fun y => by
    rw [← Scheme.Hom.comp_apply, fiberιOfMem_ι]
  haveI hinv : ∀ m : ℤ, Stacks.Ample.IsInvertibleModule 𝒞 (MMP.Chow.twistMod H F.A F.n m) :=
    fun m => Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules 𝒞
      (Stacks.Ample.tensorPowModule 𝒞 H m) (Stacks.Ample.tensorPowModule 𝒞 F.A (F.n : ℤ))
  set ω : S.residueField t →+* Γ(π.fiber t, ⊤) :=
    (Stacks.Cech.baseRingHom (π.fiberToSpecResidueField t) ⊤).hom
  -- the `κ(t)`-structure on the fibre sections
  letI : Module (S.residueField t) Γ((Scheme.Modules.pullback g').obj
      ((Scheme.Modules.pullback ι').obj (MMP.Chow.twistMod H F.A F.n (-2))), ⊤) :=
    Stacks.Cech.sectionsModule (π.fiberToSpecResidueField t) _ (g' ⁻¹ᵁ ⊤)
  letI : Module (S.residueField t) Γ((Scheme.Modules.pullback g').obj
      ((Scheme.Modules.pullback ι').obj (MMP.Chow.twistMod H F.A F.n (-2 + 1))), ⊤) :=
    Stacks.Cech.sectionsModule (π.fiberToSpecResidueField t) _ (g' ⁻¹ᵁ ⊤)
  letI : Module (S.residueField t) Γ((Scheme.Modules.pullback g').obj
      ((Scheme.Modules.pullback ι').obj (MMP.Chow.twistMod H F.A F.n (-2 + 1 + 1))), ⊤) :=
    Stacks.Cech.sectionsModule (π.fiberToSpecResidueField t) _ (g' ⁻¹ᵁ ⊤)
  have hs₂ : ∀ (c : S.residueField t) (s : Γ((Scheme.Modules.pullback g').obj
      ((Scheme.Modules.pullback ι').obj (MMP.Chow.twistMod H F.A F.n (-2))), ⊤)),
      c • s = ω c • s := fun _ _ => rfl
  have hs₁ : ∀ (c : S.residueField t) (s : Γ((Scheme.Modules.pullback g').obj
      ((Scheme.Modules.pullback ι').obj (MMP.Chow.twistMod H F.A F.n (-2 + 1))), ⊤)),
      c • s = ω c • s := fun _ _ => rfl
  have hs₀ : ∀ (c : S.residueField t) (s : Γ((Scheme.Modules.pullback g').obj
      ((Scheme.Modules.pullback ι').obj (MMP.Chow.twistMod H F.A F.n (-2 + 1 + 1))), ⊤)),
      c • s = ω c • s := fun _ _ => rfl
  obtain ⟨β₂, β₁, β₀, hM₁, hM₀⟩ : ∃ (β₂ : Module.Basis (Fin F.data.r₂) (S.residueField t)
        Γ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj
          (MMP.Chow.twistMod H F.A F.n (-2))), ⊤))
      (β₁ : Module.Basis (Fin F.data.r₁) (S.residueField t)
        Γ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj
          (MMP.Chow.twistMod H F.A F.n (-2 + 1))), ⊤))
      (β₀ : Module.Basis (Fin F.data.r₀) (S.residueField t)
        Γ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj
          (MMP.Chow.twistMod H F.A F.n (-2 + 1 + 1))), ⊤)),
      (∀ α : MMP.Chow.twistMod H F.A F.n (-2) ⟶ MMP.Chow.twistMod H F.A F.n (-2 + 1),
        LinearMap.toMatrix β₂ β₁ (appTopₗ ω hs₂ hs₁ ((Scheme.Modules.pullback g').map
          ((Scheme.Modules.pullback ι').map α))) =
        (LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π W α)).map
          (residueOfMem t ht).hom) ∧
      (∀ α : MMP.Chow.twistMod H F.A F.n (-2 + 1) ⟶ MMP.Chow.twistMod H F.A F.n (-2 + 1 + 1),
        LinearMap.toMatrix β₁ β₀ (appTopₗ ω hs₁ hs₀ ((Scheme.Modules.pullback g').map
          ((Scheme.Modules.pullback ι').map α))) =
        (LinearMap.toMatrix F.data.b₁ F.data.b₀ (MMP.Chow.directImageSectionsMap π W α)).map
          (residueOfMem t ht).hom) :=
    exists_fibreBases π F.affine
      (MMP.Chow.twistMod H F.A F.n (-2)) (MMP.Chow.twistMod H F.A F.n (-2 + 1))
      (MMP.Chow.twistMod H F.A F.n (-2 + 1 + 1)) (hinv _) (hinv _) (hinv _)
      (F.vanishing _ (Or.inl rfl)) (F.vanishing _ (Or.inr (Or.inl rfl)))
      (F.vanishing _ (Or.inr (Or.inr rfl))) F.data.b₂ F.data.b₁ F.data.b₀ t ht
  -- the pulled back hyperplane bundle and its sections
  haveI : Stacks.Ample.IsInvertibleModule (π ⁻¹ᵁ W).toScheme ((Scheme.Modules.pullback ι').obj H) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback ι' H
  haveI : Stacks.Ample.IsInvertibleModule (π.fiber t)
      ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj H)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback g' _
  set σ' : Γ(H, ⊤) → Γ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj H), ⊤) :=
    fun σ => pullbackGlobalSections g' _ (pullbackGlobalSections ι' H σ) with hσ'
  have hnv₁ : ∀ (σ : Γ(H, ⊤)) (y : π.fiber t), g' y ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback ι').obj H) (pullbackGlobalSections ι' H σ) ↔
        π.fiberι t y ∈ Stacks.Ample.nonvanishingLocus H σ := by
    intro σ y
    rw [← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections,
      Set.mem_preimage, hg'ι]
  have hnv : ∀ (σ : Γ(H, ⊤)) (y : π.fiber t), y ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj H)) (σ' σ) ↔
        π.fiberι t y ∈ Stacks.Ample.nonvanishingLocus H σ := by
    intro σ y
    rw [← hnv₁, hσ']
    rw [← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections,
      Set.mem_preimage]
  have hnvF : ∀ (σ : Γ(H, ⊤)) (y : π.fiber t), y ∈ Stacks.Ample.nonvanishingLocus
      (fibreH g π q t) (pullbackGlobalSections (π.fiberι t) H σ) ↔
        π.fiberι t y ∈ Stacks.Ample.nonvanishingLocus H σ := by
    intro σ y
    rw [← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections,
      Set.mem_preimage]
  -- a coordinate not vanishing at each point
  have hidxF : ∀ y, π.fiberι t y ∈ Stacks.Ample.nonvanishingLocus H
      (coordSection g q (fibreIdx g π q t y)) :=
    fun y => (hnvF _ y).1 (fibreIdx_mem g π q t y)
  have hidx : ∀ y, y ∈ Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj H))
      (σ' (coordSection g q (fibreIdx g π q t y))) := fun y => (hnv _ y).2 (hidxF y)
  have hidx₁ : ∀ y, g' y ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback ι').obj H)
      (pullbackGlobalSections ι' H (coordSection g q (fibreIdx g π q t y))) :=
    fun y => (hnv₁ _ y).2 (hidxF y)
  have hidx₀ : ∀ y, ι' (g' y) ∈ Stacks.Ample.nonvanishingLocus H
      (coordSection g q (fibreIdx g π q t y)) := fun y => by rw [hg'ι]; exact hidxF y
  -- the coordinates in that basis
  let crd : Γ(H, ⊤) → ∀ y : π.fiber t, (π.fiber t).presheaf.stalk y := fun σ y =>
    (Stacks.EnriquesSeveriZariski.isStalkBasis_Γgerm_of_mem_nonvanishingLocus _ _ (hidx y)).coord
      ((((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj H)).presheaf.Γgerm
        y).hom (σ' σ))
  -- the multiplications on the fibre
  let μ : Γ(H, ⊤) → ∀ m : ℤ, ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj
      (MMP.Chow.twistMod H F.A F.n m)) ⟶ (Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pullback ι').obj (MMP.Chow.twistMod H F.A F.n (m + 1)))) := fun σ m =>
    (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback ι').map
      (MMP.Chow.coordMul H F.A σ F.n m))
  have hμ : ∀ (σ : Γ(H, ⊤)) (m : ℤ) (y : π.fiber t), stalkLinearMap _ _ (μ σ m) y =
      crd σ y • stalkLinearMap _ _ (μ (coordSection g q (fibreIdx g π q t y)) m) y :=
    fun σ m y => stalkLinearMap_pullback₂_coordMul_eq g' ι' H F.A F.n m σ _ y (hidx₀ y)
      (hidx₁ y) (hidx y)
  have hμbij : ∀ (σ : Γ(H, ⊤)) (m : ℤ) (y : π.fiber t), π.fiberι t y ∈
      Stacks.Ample.nonvanishingLocus H σ → Function.Bijective (stalkLinearMap _ _ (μ σ m) y) :=
    fun σ m y hy => bijective_stalk_pullback_map g' _ y (bijective_stalk_pullback_map ι' _ (g' y)
      (bijective_stalk_coordMul H F.A σ F.n m (by rw [hg'ι]; exact hy)))
  -- the zero locus of `ℓ_a`
  have hmemZ : ∀ y, y ∈ hZfin.toFinset ↔ linForm a ∈ (fibrePsi g π q t y).asHomogeneousIdeal :=
    fun y => hZfin.mem_toFinset
  have hnvLin : ∀ y, π.fiberι t y ∈ Stacks.Ample.nonvanishingLocus H (linSection g q a) ↔
      linForm a ∉ (fibrePsi g π q t y).asHomogeneousIdeal := fun y =>
    (hnvF _ y).symm.trans (mem_nonvanishingLocus_fibreLin_iff g π q t a y)
  have hfa_unit : ∀ y, IsUnit (crd (linSection g q a) y) ↔
      linForm a ∉ (fibrePsi g π q t y).asHomogeneousIdeal := fun y =>
    (isUnit_coord_iff _ (σ' (linSection g q a)) _ (hidx y)).trans ((hnv _ y).trans (hnvLin y))
  have hfa_nzd : ∀ y, crd (linSection g q a) y ∈ nonZeroDivisors ((π.fiber t).presheaf.stalk y) :=
    fun y => coord_mem_nonZeroDivisors _ (σ' (linSection g q a)) _
      (fun ζ hζ => (hnv _ ζ).2 ((hnvLin ζ).2 (hreg ζ hζ))) (hidx y)
  -- the points of the zero locus are closed
  haveI : QuasiCompact (π.fiberι t ≫ π ≫ sS) :=
    @instQuasiCompactOfUniversallyClosed _ _ _ hFprop.toUniversallyClosed
  haveI : CompactSpace (π.fiber t) :=
    QuasiCompact.compactSpace_of_compactSpace (π.fiberι t ≫ π ≫ sS)
  haveI : AlgebraicGeometry.IsNoetherian (π.fiber t) := AlgebraicGeometry.IsNoetherian.mk
  have hZclosed : ∀ y ∈ hZfin.toFinset, IsClosed ({y} : Set (π.fiber t)) := by
    have hZ : {y | linForm a ∈ (fibrePsi g π q t y).asHomogeneousIdeal} =
        (Stacks.Ample.nonvanishingLocus (fibreH g π q t) (fibreLin g π q t a))ᶜ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, mem_nonvanishingLocus_fibreLin_iff, not_not]
    have hZc : IsClosed {y | linForm a ∈ (fibrePsi g π q t y).asHomogeneousIdeal} := by
      rw [hZ]
      exact (Stacks.NonvanishingOpen.isOpen_nonvanishingLocus _ _ _).isClosed_compl
    obtain ⟨-, hcl⟩ := finite_isClosed_of_disjoint_assoc hdimF hZc fun z hz hza => hreg z hza hz
    exact fun y hy => hcl y ((hmemZ y).1 hy)
  -- stalk bases of the fibre twists
  haveI hinvX : ∀ m : ℤ, Stacks.Ample.IsInvertibleModule (π.fiber t)
      ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj
        (MMP.Chow.twistMod H F.A F.n m))) := fun m =>
    haveI : Stacks.Ample.IsInvertibleModule (π ⁻¹ᵁ W).toScheme
        ((Scheme.Modules.pullback ι').obj (MMP.Chow.twistMod H F.A F.n m)) :=
      Stacks.InvertiblePullback.isInvertibleModule_pullback ι' _
    Stacks.InvertiblePullback.isInvertibleModule_pullback g' _
  have hbasis : ∀ (m : ℤ) (y : π.fiber t), ∃ n, Stacks.Divisors.IsStalkBasis
      ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj
        (MMP.Chow.twistMod H F.A F.n m))) y n := fun m y => by
    haveI : SheafOfModules.IsInvertible (π.fiber t).presheaf (π.fiber t).ringCatSheaf.2
        ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj
          (MMP.Chow.twistMod H F.A F.n m))) := hinvX m
    obtain ⟨V, hyV, e, he⟩ := Stacks.InvertibleStalk.exists_germ_isStalkBasis
      ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ι').obj
        (MMP.Chow.twistMod H F.A F.n m))) y
    exact ⟨_, he⟩
  -- the local equation of `ℓ_a` cuts out the zero scheme of `fibreLin`
  have hspan : ∀ y, Ideal.span {crd (linSection g q a) y} = Ideal.span {fibreEq g π q t a y} := by
    intro y
    have h1 := stalk_zeroScheme_eq_span_coord _ (σ' (linSection g q a)) _ (hidx y)
    have h2 := stalk_zeroScheme_eq_span_coord (fibreH g π q t) (fibreLin g π q t a) _
      (fibreIdx_mem g π q t y)
    haveI : SheafOfModules.IsInvertible 𝒞.sheaf.obj 𝒞.ringCatSheaf.property H :=
      (inferInstance : Stacks.Ample.IsInvertibleModule 𝒞 H)
    have h3 := Stacks.Divisors.zeroScheme_pullback_comp g' ι' H (linSection g q a)
    rw [fiberιOfMem_ι] at h3
    exact h1.symm.trans ((congrArg (fun Z => IdealSheafData.stalk Z y) h3).trans h2)
  -- the stalk cokernels of `ℓ_a` and their lengths
  have hcoker : ∀ (m : ℤ) (y : π.fiber t), Nonempty (stalkCoker (μ (linSection g q a) m) y ≃ₗ[
      (π.fiber t).presheaf.stalk y] (π.fiber t).presheaf.stalk y ⧸
        Ideal.span {crd (linSection g q a) y}) := fun m y => by
    obtain ⟨n, hn⟩ := hbasis (m + 1) y
    exact nonempty_stalkCoker_equiv _ _ y _ (hμ _ m y) (hμbij _ m y (hidxF y)).2 hn
  have hlenEq : ∀ (m : ℤ) (y : π.fiber t),
      Module.length ((π.fiber t).presheaf.stalk y) (stalkCoker (μ (linSection g q a) m) y) =
        Module.length ((π.fiber t).presheaf.stalk y)
          ((π.fiber t).presheaf.stalk y ⧸ Ideal.span {fibreEq g π q t a y}) := fun m y => by
    obtain ⟨e⟩ := hcoker m y
    rw [e.length_eq, hspan]
  have hlen_ne_top : ∀ y, Module.length ((π.fiber t).presheaf.stalk y)
      ((π.fiber t).presheaf.stalk y ⧸ Ideal.span {crd (linSection g q a) y}) ≠ ⊤ :=
    fun y => length_quotient_span_ne_top hdimF y (hfa_nzd y)
  -- injectivity and bijectivity of `ℓ_a` on stalks
  have hinjA : ∀ (m : ℤ) (y : π.fiber t),
      Function.Injective (stalkLinearMap _ _ (μ (linSection g q a) m) y) := by
    intro m y
    obtain ⟨n, hn⟩ := hbasis (m + 1) y
    have h := hμ (linSection g q a) m y
    have : (stalkLinearMap _ _ (μ (linSection g q a) m) y : _ → _) =
        (fun z => crd (linSection g q a) y • z) ∘
          stalkLinearMap _ _ (μ (coordSection g q (fibreIdx g π q t y)) m) y := by
      rw [h]
      rfl
    rw [this]
    exact (injective_smul_stalk_of_isStalkBasis hn (hfa_nzd y)).comp (hμbij _ m y (hidxF y)).1
  have hsurjA : ∀ (m : ℤ) (y : π.fiber t), y ∉ hZfin.toFinset →
      Function.Surjective (stalkLinearMap _ _ (μ (linSection g q a) m) y) := fun m y hy =>
    (hμbij _ m y ((hnvLin y).2 fun h => hy ((hmemZ y).2 h))).2
  have hflA : ∀ (m : ℤ), ∀ y ∈ hZfin.toFinset,
      IsArtinian ((π.fiber t).presheaf.stalk y) (stalkCoker (μ (linSection g q a) m) y) ∧
        IsNoetherian ((π.fiber t).presheaf.stalk y) (stalkCoker (μ (linSection g q a) m) y) :=
    fun m y _ => by
      obtain ⟨e⟩ := hcoker m y
      exact isArtinian_and_isNoetherian_of_length_ne_top e (hlen_ne_top y)
  have hdimA : ∀ m : ℤ, ∑ y ∈ hZfin.toFinset, (Module.length ((π.fiber t).presheaf.stalk y)
      (stalkCoker (μ (linSection g q a) m) y)).toNat = d := by
    intro m
    refine Eq.trans ?_ hsum
    simp only [hlenEq]
    refine (finsum_eq_sum_of_support_subset (fun y => fibreLen g π q t a y) fun y hy => ?_).symm
    rw [Finset.mem_coe, hmemZ]
    exact (hlen y).1 hy
  -- the cokernel determinant
  obtain ⟨lam, hlam, hCD⟩ := hasCokerDet_of_stalks (κ := S.residueField t) ω hs₂ hs₁ hs₀
    F.rank₁ F.rank₀ β₂ β₁ β₀
    (fun i => μ (coordSection g q i) (-2 + 1)) (μ (linSection g q a) (-2))
    (μ (linSection g q a) (-2 + 1)) hZfin.toFinset (hinjA (-2)) (hsurjA (-2)) (hinjA (-2 + 1))
    (hsurjA (-2 + 1)) (fun y => μ (coordSection g q (fibreIdx g π q t y)) (-2))
    (fun y => μ (coordSection g q (fibreIdx g π q t y)) (-2 + 1))
    (fun y _ => by
      simp only [μ, ← Functor.map_comp,
        MMP.Chow.coordMul_comm H F.A (linSection g q a) (coordSection g q (fibreIdx g π q t y))
          F.n (-2)])
    (fun y _ => hμbij _ _ y (hidxF y)) (fun y _ => hμbij _ _ y (hidxF y))
    (fun i y => crd (coordSection g q i) y) (fun i y _ => hμ _ _ y)
    (fun y hy => residueIsBase_fibre sS π t y (hZclosed y hy)) (hflA (-2)) (hflA (-2 + 1))
    (hdimA (-2)) (hdimA (-2 + 1))
  -- the constants of `ℓ_a` over `W`, and the residues
  let E' : Γ(S, W) →+* D.U.residueField x := (D.U.Γevaluation x).hom.comp (W.topIso.inv).hom
  have hE'k : ∀ c : k, E' (constOn sS W c) = kEval (D.ι ≫ sS) x c :=
    Γevaluation_topIso_inv_constOn sS W x
  let ε := (W.ι.residueFieldMap x).hom
  have hEε : ∀ r : Γ(S, W), E' r = ε ((residueOfMem t ht).hom r) := fun r =>
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom (topIso_inv_Γevaluation W x)) r
  -- the fibre matrices
  set Y₁ : Fin (N + 1) → Matrix (Fin F.data.r₁) (Fin F.data.r₂) (S.residueField t) := fun j =>
    LinearMap.toMatrix β₂ β₁ (appTopₗ ω hs₂ hs₁ (μ (coordSection g q j) (-2)))
  set Y₀ : Fin (N + 1) → Matrix (Fin F.data.r₀) (Fin F.data.r₁) (S.residueField t) := fun j =>
    LinearMap.toMatrix β₁ β₀ (appTopₗ ω hs₁ hs₀ (μ (coordSection g q j) (-2 + 1)))
  have hY₁res : ∀ σ, LinearMap.toMatrix β₂ β₁ (appTopₗ ω hs₂ hs₁ (μ σ (-2))) =
      (LinearMap.toMatrix F.data.b₂ F.data.b₁ (MMP.Chow.directImageSectionsMap π W
        (MMP.Chow.coordMul H F.A σ F.n (-2)))).map (residueOfMem t ht).hom := fun σ => hM₁ _
  have hY₀res : ∀ σ, LinearMap.toMatrix β₁ β₀ (appTopₗ ω hs₁ hs₀ (μ σ (-2 + 1))) =
      (LinearMap.toMatrix F.data.b₁ F.data.b₀ (MMP.Chow.directImageSectionsMap π W
        (MMP.Chow.coordMul H F.A σ F.n (-2 + 1)))).map (residueOfMem t ht).hom := fun σ => hM₀ _
  have hY₁ : ∀ j, (D.X₁ j).map (D.U.Γevaluation x).hom = (Y₁ j).map ε := fun j => by
    rw [KoszulFamily.toLocalFreeData_X₁, show Y₁ j = _ from hY₁res _]
    ext i l
    exact hEε _
  have hY₀ : ∀ j, (D.X₀ j).map (D.U.Γevaluation x).hom = (Y₀ j).map ε := fun j => by
    rw [KoszulFamily.toLocalFreeData_X₀, show Y₀ j = _ from hY₀res _]
    ext i l
    exact hEε _
  set a' : Fin (N + 1) → S.residueField t := fun j => (residueOfMem t ht).hom (constOn sS W (a j))
  have ha' : ∀ j, ε (a' j) = kEval (D.ι ≫ sS) x (a j) := fun j => (hEε _).symm.trans (hE'k (a j))
  have hLin₁ : LinearMap.toMatrix β₂ β₁ (appTopₗ ω hs₂ hs₁ (μ (linSection g q a) (-2))) =
      ∑ j, a' j • Y₁ j := by
    rw [hY₁res,
      directImageSectionsMap_coordMul_linSection sS sY g hgY π q hπq W F.A F.n (-2) a, map_sum]
    simp only [LinearEquiv.map_smul]
    rw [map_sum_smul]
    exact Finset.sum_congr rfl fun j _ => congrArg (a' j • ·) (hY₁res _).symm
  have hLin₀ : LinearMap.toMatrix β₁ β₀ (appTopₗ ω hs₁ hs₀ (μ (linSection g q a) (-2 + 1))) =
      ∑ j, a' j • Y₀ j := by
    rw [hY₀res,
      directImageSectionsMap_coordMul_linSection sS sY g hgY π q hπq W F.A F.n (-2 + 1) a, map_sum]
    simp only [LinearEquiv.map_smul]
    rw [map_sum_smul]
    exact Finset.sum_congr rfl fun j _ => congrArg (a' j • ·) (hY₀res _).symm
  -- injectivity of the restricted matrices
  have hinjM₁ : Function.Injective (∑ j, a' j • Y₁ j).mulVec :=
    hLin₁ ▸ injective_mulVec_toMatrix_appTopₗ ω hs₂ hs₁ β₂ β₁ _ (hinjA (-2))
  have hinjM₀ : Function.Injective (∑ j, a' j • Y₀ j).mulVec :=
    hLin₀ ▸ injective_mulVec_toMatrix_appTopₗ ω hs₁ hs₀ β₁ β₀ _ (hinjA (-2 + 1))
  rw [hLin₁, hLin₀] at hCD
  -- the determinant polynomial is nonzero
  have hlin0 : ∀ y ∈ hZfin.toFinset, (∑ i, C (lam y i) * MvPolynomial.X i :
      MvPolynomial (Fin (N + 1)) (S.residueField t)) ≠ 0 := by
    intro y hy h0
    have h1 := coeff_single_sum_C_mul_X (lam y) (fibreIdx g π q t y)
    rw [h0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
    have h2 := hlam y hy (fibreIdx g π q t y)
    have h3 : crd (coordSection g q (fibreIdx g π q t y)) y = 1 :=
      Stacks.Divisors.IsStalkBasis.coord_self _
    rw [h3, ← h1, map_zero, sub_zero] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have hQ0 : (∏ y ∈ hZfin.toFinset, (∑ i, C (lam y i) * MvPolynomial.X i) ^
      (Module.length ((π.fiber t).presheaf.stalk y)
        (stalkCoker (μ (linSection g q a) (-2)) y)).toNat :
      MvPolynomial (Fin (N + 1)) (S.residueField t)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun y hy => pow_ne_zero _ (hlin0 y hy)
  haveI : Infinite (S.residueField t) :=
    Infinite.of_injective (kEval sS t) (kEval_bijective sS t htc).1
  obtain ⟨c₀, hc₀, hres⟩ := D.exists_restrictU_eq_C_mul x hx hF' a ε Y₁ Y₀ hY₁ hY₀ a' ha'
    hinjM₁ hinjM₀ _ hCD hQ0
  -- the coordinate of a hyperplane at a point of the fibre
  have hcrdLin : ∀ (b : Fin (N + 1) → k) (y : π.fiber t), crd (linSection g q b) y =
      ∑ i, ((π.fiber t).presheaf.Γgerm y).hom (ω (kEval sS t (b i))) *
        crd (coordSection g q i) y :=
    fun b y => fibre_coord_linSection sS sY g hgY π q hπq W t ht hidx b y
  -- the zero sets of the linear forms at the points of the zero locus
  have hunitLin : ∀ (b : Fin (N + 1) → k) (y : π.fiber t), IsUnit (crd (linSection g q b) y) ↔
      linForm b ∉ (fibrePsi g π q t y).asHomogeneousIdeal := fun b y =>
    (isUnit_coord_iff _ (σ' (linSection g q b)) _ (hidx y)).trans ((hnv _ y).trans
      ((hnvF _ y).symm.trans (mem_nonvanishingLocus_fibreLin_iff g π q t b y)))
  -- each linear factor is a unit multiple of the linear form of its point
  have hbijt := kEval_bijective sS t htc
  let et : k ≃+* S.residueField t := RingEquiv.ofBijective (kEval sS t) hbijt
  haveI : IsAlgClosed (S.residueField t) := IsAlgClosed.of_ringEquiv k _ et
  have hassoc := exists_unit_sum_C_mul_X_eq_C_mul_map_ptForm (kEval sS t) hbijt ω hZfin.toFinset
    (fun y => fibrePsi g π q t y) (fun y hy => hZcl y ((hmemZ y).1 hy)) lam
    (fun b y => crd (linSection g q b) y) (fun i y => crd (coordSection g q i) y) hcrdLin
    (fun b y _ => hunitLin b y) hlam hlin0
  -- assembly
  show ∃ c : k, c ≠ 0 ∧ restrictU a F' = C c *
    ∏ᶠ y : π.fiber t, ptForm (fibrePsi g π q t y) ^ fibreLen g π q t a y
  have hsupp : (Function.mulSupport fun y : π.fiber t =>
      ptForm (fibrePsi g π q t y) ^ fibreLen g π q t a y) ⊆ (hZfin.toFinset : Set _) := by
    intro y hy
    rw [Finset.mem_coe, hmemZ]
    by_contra hn
    apply hy
    have h0 : fibreLen g π q t a y = 0 := not_not.1 fun h0 => hn ((hlen y).1 h0)
    simp [h0]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  have hlenNat : ∀ y, (Module.length ((π.fiber t).presheaf.stalk y)
      (stalkCoker (μ (linSection g q a) (-2)) y)).toNat = fibreLen g π q t a y := fun y => by
    rw [hlenEq]
    rfl
  simp only [hlenNat] at hres
  choose! u hu using hassoc
  rw [Finset.prod_congr rfl fun y hy => by rw [hu y hy]] at hres
  have hk : ε.comp (kEval sS t) = kEval (D.ι ≫ sS) x :=
    RingHom.ext fun c => residueFieldMap_kEval sS W x c
  exact exists_eq_C_mul_prod_of_map_eq (kEval sS t) (kEval (D.ι ≫ sS) x) ε hk
    (kEval_bijective (D.ι ≫ sS) x hx) hZfin.toFinset (fun y => ptForm (fibrePsi g π q t y))
    (fun y => fibreLen g π q t a y) u (restrictU a F') c₀ hc₀ hres

end FibreAssembly

end FibreRestrict

end FibreChow

end CoreLemmas

end Defs

end MMP.Chow.DeterminantCurveForm
