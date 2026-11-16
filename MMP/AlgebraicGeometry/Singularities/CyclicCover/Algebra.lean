module

public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffineSections
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceAffineModel
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceGradedForms
public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryKlt
public import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero

/-!
# Cyclic covers, round-ups of boundaries and general members (KM 2.4–5.1)

This file collects lemmas from Kollár–Mori used in the cone and basepoint-free theorems.

**Cyclic covers.** Let `N = L⁻¹` be a line bundle on a scheme `X`, `m > 0` and
`σ = ⟨·, s⟩ : Symᵐ(N) ⟶ 𝒪_X`. Over an open `U` on which `N` has a basis `t`, the cyclic cover
algebra `𝒜(L, m, s)` is `𝒪_U[T]/(Tᵐ - f)` with `f = ⟨tᵐ, s⟩`, and the zero scheme of `s` is
`V(f)`. Consequently the maps `ιᵢ : L⁻ⁱ ⟶ 𝒜(L, m, s)`, `0 ≤ i < m`, add up to an isomorphism
`⨁_{i<m} L⁻ⁱ ≅ 𝒜(L, m, s)`, multiplicative up to the reduction `ι_{k+m}(c u) = ⟨u, s⟩ ι_k(c)`.
When `m` is invertible and `s` trivialises `Lᵐ`, the cover is finite étale of degree `m`.

**Rank one sheaves.** The locally free locus of a coherent torsion free sheaf of rank one on a
normal variety has complement of codimension at least two: at points of codimension at most one
the local ring is a field or a discrete valuation ring.

**Exceptional divisors and curves.** For a klt pair `(X, Δ)` the round-up `⌈-Δ_Y⌉` of minus the
crepant boundary on a birational model is effective and exceptional; so is the round-up of the
test boundary of the basepoint-free theorem. A curve contracted by a birational morphism lies in
its exceptional set.

**General members.** A general member of a free linear system contains none of finitely many
given irreducible closed subsets.

## Main results

* `MMP.Mori.cyclicCover_local_equation`
* `MMP.Mori.cyclicCoverAlgebra_decomposition`
* `MMP.Mori.unramifiedCyclicCover_etale`
* `MMP.Mori.two_le_coheight_of_notMem_locallyFreeLocus`
* `MMP.Mori.subset_exceptionalSet_of_subsingleton_image`
* `MMP.Positivity.IsKltPair.isEffective_roundUp_neg_of_isCrepantBoundary`
* `MMP.Mori.IsBasepointFreeTieBreaker.isEffective_roundUp_tieBreakerBoundary`
* `MMP.Threefold.Bridges.exists_dense_open_inter_nonvanishingOpen_nonempty`

## Implementation notes

Sheaf isomorphisms of the cyclic cover are stated on sections over every open: bijectivity of
the relevant maps, with the presentation `Γ(X, W)[T] ⟶ Γ(Z, p⁻¹W)` surjective with kernel
`(Tᵐ - f)`. Both are proved on trivialising affine opens through the polynomial model of
`Spec_X Sym(N)` and glued along a basis of the topology. The polynomial model lemmas about
`Stacks.LineBundle.Situation` are proved here privately.

The codimension of a point is `Order.coheight` in the specialization order. That a divisor is
exceptional is stated componentwise, through `RationalMap.IsExceptional`. The base field of the
klt lemma is perfect; the basepoint-free lemma needs no perfectness, the smoothness of the log
resolution supplying the generators of top forms. A general member is a member over a dense open
of the coefficient space `kᴺ⁺¹` and of its projectivisation.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.49–2.52,
  3.2, 3.4, 3.33, 5.12, 5.17
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace MMP.Mori

section LocalEquation

open Polynomial

/-- If `τᵐ = φ f` and `(rᵢ)_{i<m} ↦ ∑ φ(rᵢ) τⁱ` is bijective, then `T ↦ τ` identifies
`R[T]/(Tᵐ - f)` with `A`. -/
private theorem ker_eval₂RingHom_of_basis {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (τ : A) (f : R) {m : ℕ} (hm : 0 < m) (hτ : τ ^ m = φ f)
    (hb : Function.Bijective fun r : Fin m → R => ∑ i, φ (r i) * τ ^ (i : ℕ)) :
    Function.Surjective (eval₂RingHom φ τ) ∧
      RingHom.ker (eval₂RingHom φ τ) = Ideal.span {Polynomial.X ^ m - C f} := by
  have hq : (Polynomial.X ^ m - C f : R[X]).Monic := monic_X_pow_sub_C f hm.ne'
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := hb.2 a
    refine ⟨∑ i : Fin m, C (r i) * Polynomial.X ^ (i : ℕ), ?_⟩
    simp [eval₂_finset_sum]
  · apply le_antisymm
    · intro P hP
      rcases subsingleton_or_nontrivial R with hR | hR
      · rw [Subsingleton.elim P 0]; exact zero_mem _
      rw [RingHom.mem_ker] at hP
      rw [Ideal.mem_span_singleton, ← modByMonic_eq_zero_iff_dvd hq]
      set Q := P %ₘ (Polynomial.X ^ m - C f)
      have hdeg : Q.natDegree < m := by
        have := natDegree_modByMonic_lt P hq (by
          intro h; have := congrArg natDegree h; simp [natDegree_X_pow_sub_C] at this; omega)
        simpa [natDegree_X_pow_sub_C] using this
      have hQ : eval₂ φ τ Q = 0 := by
        have h := modByMonic_add_div P (Polynomial.X ^ m - C f)
        have : eval₂ φ τ (Polynomial.X ^ m - C f) = 0 := by simp [hτ]
        rw [← h] at hP
        simpa [eval₂_add, eval₂_mul, this] using hP
      rw [eval₂_eq_sum_range' φ hdeg,
        ← Fin.sum_univ_eq_sum_range (fun i => φ (Q.coeff i) * τ ^ i)] at hQ
      have hz := hb.1 (a₁ := fun i : Fin m => Q.coeff i) (a₂ := 0) (by simpa using hQ)
      ext n
      by_cases hn : n < m
      · simpa using congrFun hz ⟨n, hn⟩
      · simp [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (not_lt.1 hn))]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      simp [hτ]

/-- If `ψ : R[T] → A` is surjective with kernel `(Tᵐ - f)` and `0 < m`, then
`d ↦ ψ (∑_{i<m} dᵢ Tⁱ)` is a bijection `Rᵐ ≃ A`. -/
private theorem bijective_eval_sum_of_ker_eq_span {R A : Type*} [CommRing R] [CommRing A] {m : ℕ}
    (hm : 0 < m) (f : R) (ψ : R[X] →+* A) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker ψ = Ideal.span {Polynomial.X ^ m - C f}) :
    Function.Bijective fun d : Fin m → R => ψ (∑ i : Fin m, C (d i) * Polynomial.X ^ (i : ℕ)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun g => ⟨0, ?_⟩⟩
    obtain ⟨P, rfl⟩ := hψ g
    exact congrArg ψ (Subsingleton.elim _ _)
  set q : R[X] := Polynomial.X ^ m - C f
  have hqmon : q.Monic := monic_X_pow_sub_C f hm.ne'
  have hqm : q.natDegree = m := natDegree_X_pow_sub_C
  have hdeg : ∀ d : Fin m → R,
      (∑ i : Fin m, C (d i) * Polynomial.X ^ (i : ℕ)).degree < q.degree := fun d => by
    rw [degree_eq_natDegree hqmon.ne_zero, hqm]
    exact degree_sum_fin_lt d
  refine ⟨fun d d' h => ?_, fun g => ?_⟩
  · have hdvd : q ∣ (∑ i : Fin m, C (d i) * Polynomial.X ^ (i : ℕ)) -
        ∑ i : Fin m, C (d' i) * Polynomial.X ^ (i : ℕ) := by
      rwa [← Ideal.mem_span_singleton, ← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    have hlt := (degree_sub_le _ _).trans_lt (max_lt (hdeg d) (hdeg d'))
    have h0 := sub_eq_zero.mp (((modByMonic_eq_self_iff hqmon).2 hlt).symm.trans
      ((modByMonic_eq_zero_iff_dvd hqmon).2 hdvd))
    funext j
    simpa [finset_sum_coeff, coeff_C_mul, coeff_X_pow, Fin.val_inj] using congrArg (coeff · j) h0
  · obtain ⟨P, rfl⟩ := hψ g
    have hR : P %ₘ q = ∑ i : Fin m, C ((P %ₘ q).coeff i) * Polynomial.X ^ (i : ℕ) := by
      have hlt : (P %ₘ q).natDegree < m := hqm ▸ natDegree_modByMonic_lt P hqmon (by
        intro h1; rw [h1, natDegree_one] at hqm; omega)
      conv_lhs => rw [as_sum_range' _ m hlt]
      simp [Finset.sum_range, C_mul_X_pow_eq_monomial]
    refine ⟨fun i => (P %ₘ q).coeff i, ?_⟩
    have hq0 : ψ q = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span rfl
    simp only
    rw [← hR]
    conv_rhs => rw [← modByMonic_add_div P q]
    rw [map_add, map_mul, hq0, zero_mul, add_zero]

section AffineChart

/-! ### The polynomial model of `Sym(N)` over an affine open -/

open PresheafOfModules in
/-- The degree-one sheafification unit carries `ι x` to the degree-one generator of `Sym(E)`. -/
private theorem pieceUnit_one_ι {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) (x : Γ(E, V)) :
    Stacks.SymAlgSections.pieceUnit E hV 1
        ⟨SymmetricAlgebra.ι Γ(X, V) Γ(E, V) x, SymPow.ι_mem_symmetricPowerInt_one _ _ x⟩ =
      (Scheme.Modules.symmetricAlgebraGen X E).val.app (op V) x :=
  Eq.trans ((symPowIntGradedAlgebra E.val).sheafifyGen_unit
      (𝟙 X.ringCatSheaf.obj) (symPowIntGen E.val) (op V) x).symm
    (congrArg (fun t => ((symPowIntGradedAlgebra E.val).sheafifyGen
        (𝟙 X.ringCatSheaf.obj) (symPowIntGen E.val)).val.app (op V) t)
      (PresheafOfModules.sheafifyCounitIso_inv_apply (𝟙 X.ringCatSheaf.obj) E (op V) x).symm)

variable (D : Stacks.LineBundle.Situation.{u})

/-- Over an affine open, an element of `Symᵏ(Γ(L, U))` is carried to the homogeneous function
of the corresponding section of `Symᵏ(L)`. -/
private theorem symSectionsRingEquiv_coe (U : D.X.affineOpens) (k : ℕ)
    (y : SymPow.symmetricPower k Γ(D.X, U.1) Γ(D.L, U.1)) :
    D.symSectionsRingEquiv U (y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)) =
      D.totalFunction k U.1 (Stacks.SymAlgSections.pieceUnit D.L U.2 k y) := by
  have h1 : DirectSum.decomposeRingEquiv
      (fun n : ℕ => SymPow.symmetricPower n Γ(D.X, U.1) Γ(D.L, U.1))
      (y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)) = DirectSum.of _ k y :=
    DirectSum.decompose_coe (fun n : ℕ => SymPow.symmetricPower n Γ(D.X, U.1) Γ(D.L, U.1)) y
  have h2 := Stacks.SymAlgSections.ofSymPowers_of D.L U.2 k y
  unfold Stacks.LineBundle.Situation.totalFunction
  rw [D.universalAlgebraMap_app_eq_sectionsIso U]
  show (D.sectionsIso U).hom.hom (Stacks.RelativeSpec.ungradedSectionsRingEquiv D.X
    D.symmetricAlgebra D.symmetricAlgebra_mul_comm U.2
      (Stacks.SymAlgSections.symPowersRingEquiv D.L U.2 (DirectSum.decomposeRingEquiv
        (fun n : ℕ => SymPow.symmetricPower n Γ(D.X, U.1) Γ(D.L, U.1))
          (y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1))))) = _
  rw [h1]
  exact congrArg (fun z => (D.sectionsIso U).hom.hom
    ((Stacks.RelativeSpec.ungradedCommUnit D.X D.symmetricAlgebra
      D.symmetricAlgebra_mul_comm U.1).hom z)) h2

/-- The basis vector of `Γ(L, U)` is the variable of the polynomial model. -/
private theorem polynomialAlgEquiv_ι (U : D.X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U.1) Γ(D.L, U.1)) :
    D.polynomialAlgEquiv U b (SymmetricAlgebra.ι Γ(D.X, U.1) Γ(D.L, U.1) (b PUnit.unit)) =
      Polynomial.X := by
  unfold Stacks.LineBundle.Situation.polynomialAlgEquiv
  rw [AlgEquiv.trans_apply, SymmetricAlgebra.equivMvPolynomial_ι_apply]
  simp

/-- Under the polynomial model, `Symᵏ(Γ(L, U))` lands in the monomials of degree `k`. -/
private theorem polynomialAlgEquiv_mem_range_monomial (U : D.X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U.1) Γ(D.L, U.1)) (k : ℕ)
    {y : SymmetricAlgebra Γ(D.X, U.1) Γ(D.L, U.1)}
    (hy : y ∈ SymPow.symmetricPower k Γ(D.X, U.1) Γ(D.L, U.1)) :
    D.polynomialAlgEquiv U b y ∈
      LinearMap.range (monomial k : Γ(D.X, U.1) →ₗ[Γ(D.X, U.1)] _) := by
  induction k generalizing y with
  | zero =>
      rw [SymPow.symmetricPower, pow_zero, Submodule.one_eq_range] at hy
      obtain ⟨c, rfl⟩ := hy
      exact ⟨c, by simp⟩
  | succ k ih =>
      rw [SymPow.symmetricPower, pow_succ] at hy
      refine Submodule.mul_induction_on hy (fun y₁ hy₁ y₂ hy₂ => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
      · obtain ⟨c₁, hc₁⟩ := ih hy₁
        obtain ⟨m, rfl⟩ := hy₂
        have hspan : m ∈ Submodule.span Γ(D.X, U.1) {b PUnit.unit} := by
          have := b.mem_span m
          rwa [Set.range_unique] at this
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hspan
        refine ⟨c₁ * c, ?_⟩
        rw [map_mul (D.polynomialAlgEquiv U b), ← hc₁, map_smul, map_smul,
          polynomialAlgEquiv_ι, Polynomial.smul_eq_C_mul, ← Polynomial.monomial_zero_left,
          ← Polynomial.monomial_one_one_eq_X, monomial_mul_monomial, monomial_mul_monomial]
        simp
      · rw [map_add]; exact Submodule.add_mem _ h₁ h₂

/-- Over an affine open, a section of `Symᵏ(L)` is determined by its homogeneous function. -/
private theorem totalFunction_injective [D.L.IsQuasicoherent] (U : D.X.affineOpens) (k : ℕ) :
    Function.Injective (D.totalFunction k U.1) := by
  intro x y h
  obtain ⟨x', rfl⟩ := (Stacks.SymAlgSections.pieceUnit D.L U.2 k).surjective x
  obtain ⟨y', rfl⟩ := (Stacks.SymAlgSections.pieceUnit D.L U.2 k).surjective y
  rw [← symSectionsRingEquiv_coe, ← symSectionsRingEquiv_coe] at h
  exact congrArg _ (Subtype.ext ((D.symSectionsRingEquiv U).injective h))

end AffineChart

section Gluing

/-! ### Freeness of rank one is local -/

variable {X : Scheme.{u}} (M : X.Modules)

private theorem modules_map_map {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (x : M.val.obj (op W)) :
    M.val.map (homOfLE h').op (M.val.map (homOfLE h).op x) =
      M.val.map (homOfLE (h'.trans h)).op x := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

private theorem presheaf_map_map {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W')
    (x : Γ(X, W)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE (h'.trans h)).op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The affine opens contained in `W` cover `W`. -/
private theorem le_iSup_affineOpens (W : X.Opens) :
    W ≤ ⨆ V : {V : X.affineOpens // V.1 ≤ W}, V.1.1 := by
  intro x hx
  obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩

/-- Two sections of `𝒪_X` over `W` agreeing on every affine open in `W` are equal. -/
private theorem presheaf_eq_of_affine {W : X.Opens} (a a' : Γ(X, W))
    (h : ∀ V : X.affineOpens, ∀ hV : V.1 ≤ W,
      X.presheaf.map (homOfLE hV).op a = X.presheaf.map (homOfLE hV).op a') : a = a' :=
  TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun V : {V : X.affineOpens // V.1 ≤ W} => V.1.1) W
    (fun V => homOfLE V.2) (le_iSup_affineOpens W) a a' fun V => h V.1 V.2

/-- Two sections of `M` over `W` agreeing on every affine open in `W` are equal. -/
private theorem modules_eq_of_affine {W : X.Opens} (x x' : M.val.obj (op W))
    (h : ∀ V : X.affineOpens, ∀ hV : V.1 ≤ W,
      M.val.map (homOfLE hV).op x = M.val.map (homOfLE hV).op x') : x = x' :=
  TopCat.Sheaf.eq_of_locally_eq' (C := Ab.{u}) ⟨M.val.presheaf, M.isSheaf⟩
    (fun V : {V : X.affineOpens // V.1 ≤ W} => V.1.1) W
    (fun V => homOfLE V.2) (le_iSup_affineOpens W) x x' fun V => h V.1 V.2

/-- If a compatible family `e_W ∈ M(W)`, `W ⊆ U`, is a basis over every affine `W ⊆ U`, it is a
basis over every open `W ⊆ U`. -/
private theorem bijective_smul_of_affine (U : X.Opens)
    (e : ∀ W : X.Opens, W ≤ U → M.val.obj (op W))
    (he : ∀ (W W' : X.Opens) (hW : W ≤ U) (h : W' ≤ W),
      M.val.map (homOfLE h).op (e W hW) = e W' (h.trans hW))
    (haff : ∀ (V : X.affineOpens) (hV : V.1 ≤ U),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V.1) => a • e V.1 hV)
    (W : X.Opens) (hW : W ≤ U) :
    Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W) => a • e W hW := by
  have hres : ∀ (W' : X.Opens) (h : W' ≤ W) (a : X.ringCatSheaf.obj.obj (op W)),
      M.val.map (homOfLE h).op (a • e W hW) =
        (show X.ringCatSheaf.obj.obj (op W') from X.presheaf.map (homOfLE h).op a) •
          e W' (h.trans hW) := by
    intro W' h a
    rw [PresheafOfModules.map_smul, he]
    rfl
  -- the coefficient of a section over an affine open in `W`
  have huniq : ∀ (V : X.affineOpens) (hV : V.1 ≤ W) (b b' : Γ(X, V.1)),
      (show X.ringCatSheaf.obj.obj (op V.1) from b) • e V.1 (hV.trans hW) =
        (show X.ringCatSheaf.obj.obj (op V.1) from b') • e V.1 (hV.trans hW) → b = b' :=
    fun V hV b b' h => (haff V (hV.trans hW)).1 h
  refine ⟨fun a a' h => presheaf_eq_of_affine a a' fun V hV => huniq V hV _ _ ?_, fun y => ?_⟩
  · rw [← hres, ← hres]
    exact congrArg _ h
  · have hc : ∀ V : {V : X.affineOpens // V.1 ≤ W}, ∃ c : Γ(X, V.1.1),
        (show X.ringCatSheaf.obj.obj (op V.1.1) from c) • e V.1.1 (V.2.trans hW) =
          M.val.map (homOfLE V.2).op y :=
      fun V => (haff V.1 (V.2.trans hW)).2 _
    choose c hc using hc
    obtain ⟨a, ha, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf
      (fun V : {V : X.affineOpens // V.1 ≤ W} => V.1.1) W (fun V => homOfLE V.2)
      (le_iSup_affineOpens W) c (by
        intro V₁ V₂
        refine presheaf_eq_of_affine _ _ fun V hV => huniq V (hV.trans (inf_le_left.trans V₁.2))
          _ _ ?_
        have h₁ := congrArg (M.val.map (homOfLE (hV.trans inf_le_left)).op) (hc V₁)
        have h₂ := congrArg (M.val.map (homOfLE (hV.trans inf_le_right)).op) (hc V₂)
        rw [PresheafOfModules.map_smul, he, modules_map_map] at h₁ h₂
        erw [presheaf_map_map, presheaf_map_map]
        exact h₁.trans h₂.symm)
    refine ⟨a, modules_eq_of_affine M _ _ fun V hV => ?_⟩
    change M.val.map (homOfLE hV).op
      ((show X.ringCatSheaf.obj.obj (op W) from a) • e W hW) = _
    rw [hres]
    have := hc ⟨V, hV⟩
    rw [← this]
    exact congrArg (· • _) (ha ⟨V, hV⟩)

/-- A family of maps `Φ_W : (ι → F(W)) → G(W)`, `W ⊆ U`, between sections of two sheaves that
commutes with restriction and is bijective on the members of a basis inside `U` is bijective
on every open `W ⊆ U`. -/
private theorem bijective_of_isBasis {T : TopCat.{u}} {ι : Type*}
    (F G : TopCat.Sheaf CommRingCat.{u} T) (B : Set (Opens T)) (hB : Opens.IsBasis B)
    (U : Opens T)
    (Φ : ∀ W : Opens T, W ≤ U → (ι → ToType (F.obj.obj (op W))) → ToType (G.obj.obj (op W)))
    (hΦ : ∀ (W W' : Opens T) (hW : W ≤ U) (h : W' ≤ W) x,
      Φ W' (h.trans hW) (fun i => F.obj.map (homOfLE h).op (x i)) =
        G.obj.map (homOfLE h).op (Φ W hW x))
    (hbij : ∀ V ∈ B, ∀ hV : V ≤ U, Function.Bijective (Φ V hV))
    (W : Opens T) (hW : W ≤ U) : Function.Bijective (Φ W hW) := by
  have hinj : ∀ (W : Opens T) (hW : W ≤ U), Function.Injective (Φ W hW) := by
    intro W hW x y hxy
    choose V hVB hzV hVW using fun z : W => Opens.isBasis_iff_nbhd.mp hB z.2
    funext i
    refine TopCat.Sheaf.eq_of_locally_eq' F V W (fun z => homOfLE (hVW z))
      (fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩) _ _ fun z => ?_
    exact congrFun ((hbij (V z) (hVB z) ((hVW z).trans hW)).1
      ((hΦ W (V z) hW (hVW z) x).trans ((congrArg _ hxy).trans
        (hΦ W (V z) hW (hVW z) y).symm))) i
  refine ⟨hinj W hW, fun g => ?_⟩
  choose V hVB hzV hVW using fun z : W => Opens.isBasis_iff_nbhd.mp hB z.2
  have hcov : W ≤ iSup V := fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩
  choose x hx using fun z => (hbij (V z) (hVB z) ((hVW z).trans hW)).2
    (G.obj.map (homOfLE (hVW z)).op g)
  have hcompat : ∀ z z', (fun i => F.obj.map (homOfLE inf_le_left : V z ⊓ V z' ⟶ V z).op
      (x z i)) = (fun i => F.obj.map (homOfLE inf_le_right : V z ⊓ V z' ⟶ V z').op (x z' i)) := by
    intro z z'
    apply hinj (V z ⊓ V z') (inf_le_left.trans ((hVW z).trans hW))
    rw [hΦ (V z) (V z ⊓ V z') ((hVW z).trans hW) inf_le_left,
      hΦ (V z') (V z ⊓ V z') ((hVW z').trans hW) inf_le_right, hx, hx,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← G.obj.map_comp, ← G.obj.map_comp]
    rfl
  choose s hs _ using fun i => TopCat.Sheaf.existsUnique_gluing' F V W
    (fun z => homOfLE (hVW z)) hcov (fun z => x z i) (fun z z' => congrFun (hcompat z z') i)
  refine ⟨s, TopCat.Sheaf.eq_of_locally_eq' G V W (fun z => homOfLE (hVW z)) hcov _ _
    fun z => ?_⟩
  rw [← hΦ W (V z) hW (hVW z), ← hx z]
  congr 1
  funext i
  exact hs i z

end Gluing

section Geometry

variable {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (m : ℕ) (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf)

private theorem gen_nat (U W : X.Opens) (hW : W ≤ U) (t : N.val.obj (op U)) :
    (cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W) (N.val.map (homOfLE hW).op t) =
      ((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.map (homOfLE hW).op
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op U) t) :=
  PresheafOfModules.naturality_apply (cyclicCoverSituation N).symmetricAlgebraGen.val
    (homOfLE hW).op t

private theorem incl_nat (k : ℕ) (U W : X.Opens) (hW : W ≤ U)
    (x : ((cyclicCoverSituation N).symmetricAlgebra.piece (k : ℤ)).val.obj (op U)) :
    cyclicCoverAlgebraIncl N m σ k W
        (((cyclicCoverSituation N).symmetricAlgebra.piece (k : ℤ)).val.map (homOfLE hW).op x) =
      (cyclicCover N m σ).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ hW)).op
        (cyclicCoverAlgebraIncl N m σ k U x) := by
  have h1 := symSpecFunction_restrict N k hW x
  have h2 := ConcreteCategory.congr_hom (Scheme.Hom.naturality (cyclicCoverIdeal N m σ).subschemeι
    (homOfLE (Scheme.Hom.preimage_mono (symSpecToBase N) hW)).op) (symSpecFunction N k U x)
  unfold cyclicCoverAlgebraIncl
  refine (congrArg _ h1.symm).trans ?_
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h2
  exact h2

private theorem incl_cast (U : X.Opens) {n n' : ℤ} (h : n = n')
    (z : ((cyclicCoverSituation N).symmetricAlgebra.piece n).val.obj (op U)) :
    (cyclicCoverSituation N).algebraSheafIncl n' U
      ((eqToHom (congrArg (cyclicCoverSituation N).symmetricAlgebra.piece h)).val.app (op U) z) =
      (cyclicCoverSituation N).algebraSheafIncl n U z := by
  subst h; rfl

private theorem tau_pow (hm : 0 < m) (U : X.Opens) (t : N.val.obj (op U))
    (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op U))
    (hu : (cyclicCoverSituation N).algebraSheafIncl m U u =
      (cyclicCoverSituation N).algebraSheafIncl 1 U
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op U) t) ^ m)
    (f : Γ(X, U)) (hf : σ.val.app (op U) u = f) (W : X.Opens) (hW : W ≤ U) :
    cyclicCoverAlgebraIncl N m σ 1 W
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
          (N.val.map (homOfLE hW).op t)) ^ m =
      ((cyclicCoverToBase N m σ).app W).hom (X.presheaf.map (homOfLE hW).op f) := by
  have hU : cyclicCoverAlgebraIncl N m σ 1 U
      ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op U) t) ^ m =
      ((cyclicCoverToBase N m σ).app U).hom f := by
    rw [← hf, ← cyclicCoverAlgebraIncl_self N m σ U u]
    unfold cyclicCoverAlgebraIncl symSpecFunction
    rw [hu]; erw [map_pow, map_pow]; rfl
  rw [gen_nat N U W hW t]
  erw [incl_nat N m σ 1 U W hW]
  erw [← map_pow, hU]
  have h2 := ConcreteCategory.congr_hom (Scheme.Hom.naturality (cyclicCoverToBase N m σ)
    (homOfLE hW).op) f
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h2
  exact h2.symm

/-- The powers `tⁱ ∈ Γ(W, Symⁱ N)` of a section `t ∈ Γ(W, N)`, built from the graded product. -/
private noncomputable def symPow {W : X.Opens}
    (g : ((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.obj (op W)) :
    ∀ i : ℕ, ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.obj (op W)
  | 0 => (cyclicCoverSituation N).symmetricAlgebra.one.eval (op W)
  | i + 1 => (eqToHom (congrArg (cyclicCoverSituation N).symmetricAlgebra.piece
      (Nat.cast_succ i).symm)).val.app (op W)
      (((cyclicCoverSituation N).symmetricAlgebra.mul (i : ℤ) 1).app (op W) (symPow g i) g)

private theorem incl_symPow {W : X.Opens}
    (g : ((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.obj (op W)) (i : ℕ) :
    (cyclicCoverSituation N).algebraSheafIncl i W (symPow N g i) =
      (cyclicCoverSituation N).algebraSheafIncl 1 W g ^ i := by
  induction i with
  | zero => exact ((cyclicCoverSituation N).algebraSheafIncl_one W).trans (pow_zero _).symm
  | succ i ih =>
    rw [symPow, incl_cast N W (Nat.cast_succ i).symm,
      ← (cyclicCoverSituation N).algebraSheafIncl_mul, ih, pow_succ]

/-- The function on `Spec_X Sym(N)` attached to `gⁱ` is the `i`-th power of that of `g`. -/
private theorem symSpecFunction_symPow {W : X.Opens}
    (g : ((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.obj (op W)) (i : ℕ) :
    symSpecFunction N i W (symPow N g i) = symSpecFunction N 1 W g ^ i := by
  unfold symSpecFunction
  rw [incl_symPow]
  exact map_pow _ _ _

/-- Over an affine open `V` on which `N` has the basis `b`, the function attached to the
degree-one generator `b` is the variable of the polynomial model. -/
private theorem symSpecFunction_gen_basis (V : X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(X, V.1) Γ(N, V.1)) :
    symSpecFunction N 1 V.1
      ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V.1) (b PUnit.unit)) =
      (cyclicCoverSituation N).polynomialSectionsRingEquiv V b Polynomial.X := by
  have e : ((cyclicCoverSituation N).polynomialAlgEquiv V b).symm Polynomial.X =
      SymmetricAlgebra.ι Γ(X, V.1) Γ(N, V.1) (b PUnit.unit) := by
    rw [AlgEquiv.symm_apply_eq, polynomialAlgEquiv_ι]
  have h2 := symSectionsRingEquiv_coe (cyclicCoverSituation N) V 1
    ⟨SymmetricAlgebra.ι Γ(X, V.1) Γ(N, V.1) (b PUnit.unit),
      SymPow.ι_mem_symmetricPowerInt_one _ _ _⟩
  refine Eq.trans ?_ ((congrArg _ e).trans (h2.trans
    (congrArg _ (pieceUnit_one_ι N V.2 (b PUnit.unit))))).symm
  rfl

/-- Over an affine open `V` on which `N` has the basis `b`, the function on `Spec_X Sym(N)`
attached to `a • bⁱ` is the monomial `a Tⁱ` of the polynomial model. -/
private theorem symSpecFunction_smul_symPow (V : X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(X, V.1) Γ(N, V.1)) (i : ℕ) (a : Γ(X, V.1)) :
    symSpecFunction N i V.1 ((show X.ringCatSheaf.obj.obj (op V.1) from a) • symPow N
      ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V.1) (b PUnit.unit)) i) =
    (cyclicCoverSituation N).polynomialSectionsRingEquiv V b (monomial i a) := by
  rw [symSpecFunction_smul, symSpecFunction_symPow, symSpecFunction_gen_basis,
    ← C_mul_X_pow_eq_monomial, map_mul, map_pow,
    (cyclicCoverSituation N).polynomialSectionsRingEquiv_C]

/-- Over an affine open `V` on which `N` has the basis `b`, `Symⁱ(N)(V)` is free of rank one
with basis `bⁱ`. -/
private theorem smul_symPow_bijective_of_basis (V : X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(X, V.1) Γ(N, V.1)) (i : ℕ) :
    Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V.1) => a • symPow N
      ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op V.1) (b PUnit.unit)) i := by
  refine ⟨fun a a' h => ?_, fun y => ?_⟩
  · have := congrArg (symSpecFunction N i V.1) h
    exact Polynomial.monomial_injective i
      (((cyclicCoverSituation N).polynomialSectionsRingEquiv V b).injective
        ((symSpecFunction_smul_symPow N V b i a).symm.trans
          (this.trans (symSpecFunction_smul_symPow N V b i a'))))
  · obtain ⟨y', rfl⟩ := (Stacks.SymAlgSections.pieceUnit N V.2 i).surjective y
    obtain ⟨c, hc⟩ := polynomialAlgEquiv_mem_range_monomial (cyclicCoverSituation N) V b i y'.2
    refine ⟨c, totalFunction_injective (cyclicCoverSituation N) V i ?_⟩
    refine (symSpecFunction_smul_symPow N V b i c).trans ?_
    rw [← symSectionsRingEquiv_coe]
    change (cyclicCoverSituation N).symSectionsRingEquiv V
      (((cyclicCoverSituation N).polynomialAlgEquiv V b).symm (monomial i c)) = _
    rw [show (monomial i c : Γ(X, V.1)[X]) =
      (cyclicCoverSituation N).polynomialAlgEquiv V b y' from hc, AlgEquiv.symm_apply_apply]

/-- The powers `tⁱ` commute with restriction. -/
private theorem symPow_map {W W' : X.Opens} (h : W' ≤ W)
    (g : ((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.obj (op W)) :
    ∀ i : ℕ, ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.map (homOfLE h).op
        (symPow N g i) =
      symPow N (((cyclicCoverSituation N).symmetricAlgebra.piece 1).val.map (homOfLE h).op g) i
  | 0 => PresheafOfModules.sections_property _ _
  | i + 1 => by
    simp only [symPow]
    refine (PresheafOfModules.naturality_apply (eqToHom (congrArg
      (cyclicCoverSituation N).symmetricAlgebra.piece (Nat.cast_succ i).symm)).val
        (homOfLE h).op _).symm.trans (congrArg _ ?_)
    refine (((cyclicCoverSituation N).symmetricAlgebra.mul (i : ℤ) 1).naturality _ _ _).trans ?_
    exact congrArg (fun z => (((cyclicCoverSituation N).symmetricAlgebra.mul (i : ℤ) 1).app
      (op W')) z _) (symPow_map h g i)

/-- A section `t` such that `a ↦ a • t` is bijective over `V` gives a `PUnit`-indexed basis of
`Γ(N, V)`. -/
private noncomputable def basisOfBijective {V : X.Opens} (t : N.val.obj (op V))
    (ht : Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V) => a • t) :
    Module.Basis PUnit.{u + 1} Γ(X, V) Γ(N, V) :=
  (Module.Basis.singleton PUnit.{u + 1} Γ(X, V)).map
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, V) Γ(N, V) t) ht)

private theorem basisOfBijective_apply {V : X.Opens} (t : N.val.obj (op V))
    (ht : Function.Bijective fun a : X.ringCatSheaf.obj.obj (op V) => a • t) :
    basisOfBijective N t ht PUnit.unit = t := by
  simp only [basisOfBijective, Module.Basis.map_apply, Module.Basis.singleton_apply]
  exact one_smul _ _

/-- Over `W ⊆ U`, `Symⁱ(N)(W)` is free of rank one with basis `tⁱ`. -/
private theorem symPow_smul_bijective (U : X.Opens) (t : N.val.obj (op U))
    (ht : ∀ (W : X.Opens) (hW : W ≤ U),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W) =>
        a • (N.val.map (homOfLE hW).op t : N.val.obj (op W)))
    (W : X.Opens) (hW : W ≤ U) (i : ℕ) :
    Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W) =>
      a • symPow N ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
        (N.val.map (homOfLE hW).op t)) i := by
  refine bijective_smul_of_affine _ U (fun W hW => symPow N
    ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
      (N.val.map (homOfLE hW).op t)) i) (fun W W' hW h => ?_) (fun V hV => ?_) W hW
  · rw [symPow_map]
    exact congrArg (symPow N · i)
      ((gen_nat N W W' h _).symm.trans (congrArg _ (modules_map_map N hW h t)))
  · have := smul_symPow_bijective_of_basis N V (basisOfBijective N _ (ht V.1 hV)) i
    convert this using 5
    exact congrArg _ (basisOfBijective_apply N _ _).symm

/-- A section of a quasi-coherent module over a standard open `D(r)` of an affine open `W₀`
becomes, after multiplication by a power of `r`, the restriction of a section over `W₀`. -/
private theorem exists_map_eq_pow_smul (M : X.Modules) [M.IsQuasicoherent] (W₀ : X.affineOpens)
    (r : Γ(X, W₀.1)) (u : M.val.obj (op (X.basicOpen r))) :
    ∃ (x : M.val.obj (op W₀.1)) (k : ℕ), M.val.map (homOfLE (X.basicOpen_le r)).op x =
      (show X.ringCatSheaf.obj.obj (op (X.basicOpen r)) from
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op r) ^ k) • u := by
  letI := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE M (X.basicOpen_le r)
  haveI := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ
    M W₀.2 r rfl (X.basicOpen_le r)
  obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers r)
    (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ M (X.basicOpen_le r)) u
  refine ⟨x, k, ?_⟩
  rw [← map_pow]
  exact hx.symm

/-- The image ideals `(⟨·, s⟩(Symᵐ(N)(V)))` on the affine opens `V` form an ideal sheaf. -/
private noncomputable def zeroSchemeIdealData : X.IdealSheafData where
  ideal V := Ideal.span (Set.range (σ.val.app (op V.1)))
  map_ideal_basicOpen V g := by
    haveI := (cyclicCoverSituation N).isQuasicoherent_symmetricAlgebra_piece m
    rw [Ideal.map_span]
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨_, PresheafOfModules.naturality_apply σ.val _ x⟩
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨w, rfl⟩
      obtain ⟨x, k, hx⟩ := exists_map_eq_pow_smul _ V g w
      have hu := (X.toRingedSpace.isUnit_res_basicOpen g).pow k
      refine (Ideal.unit_mul_mem_iff_mem _ hu).mp ?_
      have : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) ^ k *
          (show Γ(X, X.basicOpen g) from σ.val.app (op (X.basicOpen g)) w) =
          σ.val.app (op (X.basicOpen g))
            (((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.map
              (homOfLE (X.basicOpen_le g)).op x) := by
        rw [hx]
        exact ((σ.val.app (op (X.basicOpen g))).hom.map_smul _ w).symm
      erw [this]
      rw [PresheafOfModules.naturality_apply]
      exact Ideal.subset_span ⟨_, ⟨x, rfl⟩, rfl⟩

private theorem zeroSchemeIdeal_ideal (V : X.affineOpens) :
    (zeroSchemeIdeal N m σ).ideal V = (zeroSchemeIdealData N m σ).ideal V := by
  rw [show zeroSchemeIdeal N m σ = zeroSchemeIdealData N m σ from
    Scheme.IdealSheafData.ofIdeals_ideal (zeroSchemeIdealData N m σ)]

/-- On affine `W ⊆ U`, the section `u|_W` of `Symᵐ(N)` is `tᵐ` and `⟨tᵐ, s⟩ = f|_W`. -/
private theorem sigma_symPow (U : X.Opens) (t : N.val.obj (op U))
    (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op U))
    (hu : (cyclicCoverSituation N).algebraSheafIncl m U u =
      (cyclicCoverSituation N).algebraSheafIncl 1 U
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op U) t) ^ m)
    (f : Γ(X, U)) (hf : σ.val.app (op U) u = f) (W : X.affineOpens) (hW : W.1 ≤ U) :
    σ.val.app (op W.1) (symPow N ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W.1)
      (N.val.map (homOfLE hW).op t)) m) = X.presheaf.map (homOfLE hW).op f := by
  set g := (cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W.1)
    (N.val.map (homOfLE hW).op t)
  have hue : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.map (homOfLE hW).op u =
      symPow N g m := by
    apply totalFunction_injective (cyclicCoverSituation N) W m
    change symSpecFunction N m W.1 _ = symSpecFunction N m W.1 _
    have hU : symSpecFunction N m U u = symSpecFunction N 1 U
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op U) t) ^ m := by
      unfold symSpecFunction
      rw [hu]
      exact map_pow _ _ _
    rw [← symSpecFunction_restrict N m hW u, hU, symSpecFunction_symPow, map_pow]
    erw [symSpecFunction_restrict N 1 hW]
    exact congrArg (fun z => symSpecFunction N 1 W.1 z ^ m) (gen_nat N U W.1 hW t).symm
  rw [← hue, PresheafOfModules.naturality_apply, hf]
  rfl

/-- On affine `W ⊆ U`, the ideal of `(s = 0)` is `(f)`. -/
private theorem zeroSchemeIdeal_ideal_eq (U : X.Opens) (t : N.val.obj (op U))
    (ht : ∀ (W : X.Opens) (hW : W ≤ U),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W) =>
        a • (N.val.map (homOfLE hW).op t : N.val.obj (op W)))
    (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op U))
    (hu : (cyclicCoverSituation N).algebraSheafIncl m U u =
      (cyclicCoverSituation N).algebraSheafIncl 1 U
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op U) t) ^ m)
    (f : Γ(X, U)) (hf : σ.val.app (op U) u = f) (W : X.affineOpens) (hW : W.1 ≤ U) :
    (zeroSchemeIdeal N m σ).ideal W = Ideal.span {X.presheaf.map (homOfLE hW).op f} := by
  rw [zeroSchemeIdeal_ideal]
  set g := (cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W.1)
    (N.val.map (homOfLE hW).op t)
  have hfW := sigma_symPow N m σ U t u hu f hf W hW
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := (symPow_smul_bijective N U t ht W.1 hW m).2 x
    change σ.val.app (op W.1) (a • symPow N g m) ∈
      (Ideal.span {X.presheaf.map (homOfLE hW).op f} : Ideal Γ(X, W.1))
    rw [(σ.val.app (op W.1)).hom.map_smul]
    erw [hfW]
    exact Ideal.mul_mem_left _ a (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨_, hfW⟩

/-- The generator `τ = ι₁(t)` restricts to the generator over a smaller open. -/
private theorem tau_restrict (U : X.Opens) (t : N.val.obj (op U)) {W W' : X.Opens}
    (hW : W ≤ U) (h : W' ≤ W) :
    cyclicCoverAlgebraIncl N m σ 1 W'
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W')
          (N.val.map (homOfLE (h.trans hW)).op t)) =
      (cyclicCover N m σ).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op
        (cyclicCoverAlgebraIncl N m σ 1 W
          ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
            (N.val.map (homOfLE hW).op t))) := by
  rw [← modules_map_map N hW h t]
  erw [gen_nat N W W' h (N.val.map (homOfLE hW).op t)]
  exact incl_nat N m σ 1 W W' h _

/-- **The local equation over an affine open.** On an affine `W ⊆ U`, `T ↦ τ` identifies
`Γ(X, W)[T]/(Tᵐ - f)` with `Γ(Z, p⁻¹W)`: through the polynomial model
`Γ(Spec_X Sym(N), π⁻¹W) = Γ(X, W)[T]`, the ideal of `Z` is generated by the
`a (tᵐ - ⟨tᵐ, s⟩) = a (Tᵐ - f)`. -/
private theorem eval₂_of_isAffineOpen (U : X.Opens) (t : N.val.obj (op U))
    (ht : ∀ (W : X.Opens) (hW : W ≤ U),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W) =>
        a • (N.val.map (homOfLE hW).op t : N.val.obj (op W)))
    (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op U))
    (hu : (cyclicCoverSituation N).algebraSheafIncl m U u =
      (cyclicCoverSituation N).algebraSheafIncl 1 U
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op U) t) ^ m)
    (f : Γ(X, U)) (hf : σ.val.app (op U) u = f) (W : X.affineOpens) (hW : W.1 ≤ U) :
    Function.Surjective (Polynomial.eval₂RingHom ((cyclicCoverToBase N m σ).app W.1).hom
        (cyclicCoverAlgebraIncl N m σ 1 W.1
          ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W.1)
            (N.val.map (homOfLE hW).op t)))) ∧
      RingHom.ker (Polynomial.eval₂RingHom ((cyclicCoverToBase N m σ).app W.1).hom
        (cyclicCoverAlgebraIncl N m σ 1 W.1
          ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W.1)
            (N.val.map (homOfLE hW).op t)))) =
        Ideal.span {Polynomial.X ^ m - Polynomial.C (X.presheaf.map (homOfLE hW).op f)} := by
  set g := (cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W.1)
    (N.val.map (homOfLE hW).op t)
  let b := basisOfBijective N _ (ht W.1 hW)
  have hb : b PUnit.unit = N.val.map (homOfLE hW).op t := basisOfBijective_apply N _ _
  set Ψ := (cyclicCoverSituation N).polynomialSectionsRingEquiv W b
  let V : (symSpec N).affineOpens := ⟨_, W.2.preimage (symSpecToBase N)⟩
  let ρ : Γ(symSpec N, symSpecToBase N ⁻¹ᵁ W.1) →+*
      Γ(cyclicCover N m σ, cyclicCoverToBase N m σ ⁻¹ᵁ W.1) :=
    ((cyclicCoverIdeal N m σ).subschemeι.app (symSpecToBase N ⁻¹ᵁ W.1)).hom
  have hX : Ψ Polynomial.X = symSpecFunction N 1 W.1 g := by
    rw [← symSpecFunction_gen_basis, hb]
  have hρΨ : ρ.comp Ψ.toRingHom = Polynomial.eval₂RingHom
      ((cyclicCoverToBase N m σ).app W.1).hom (cyclicCoverAlgebraIncl N m σ 1 W.1 g) := by
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · change ρ (Ψ (Polynomial.C r)) = _
      rw [(cyclicCoverSituation N).polynomialSectionsRingEquiv_C, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      unfold cyclicCoverToBase
      rw [Scheme.Hom.comp_app]
      rfl
    · change ρ (Ψ Polynomial.X) = _
      rw [hX, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  rw [← hρΨ]
  refine ⟨(Scheme.IdealSheafData.subschemeι_app_surjective _ V).comp Ψ.surjective, ?_⟩
  have hq : cyclicCoverGenerator N m σ W.1 (symPow N g m) =
      Ψ (Polynomial.X ^ m - Polynomial.C (X.presheaf.map (homOfLE hW).op f)) := by
    unfold cyclicCoverGenerator
    rw [sigma_symPow N m σ U t u hu f hf W hW, map_sub, map_pow, hX,
      (cyclicCoverSituation N).polynomialSectionsRingEquiv_C]
    exact congrArg (· - _) (symSpecFunction_symPow N g m)
  have hid : ∀ y, (symSpec N).presheaf.map (homOfLE (le_refl (symSpecToBase N ⁻¹ᵁ W.1))).op y =
      y := fun y => by
    rw [show homOfLE (le_refl (symSpecToBase N ⁻¹ᵁ W.1)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  have hspan : (cyclicCoverIdeal N m σ).ideal V =
      Ideal.span {Ψ (Polynomial.X ^ m - Polynomial.C (X.presheaf.map (homOfLE hW).op f))} := by
    rw [ideal_cyclicCoverIdeal N m σ W V le_rfl]
    apply le_antisymm
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := (symPow_smul_bijective N U t ht W.1 hW m).2 x
      change (symSpec N).presheaf.map (homOfLE (le_refl (symSpecToBase N ⁻¹ᵁ W.1))).op
        (cyclicCoverGenerator N m σ W.1 (a • symPow N g m)) ∈ _
      rw [hid, cyclicCoverGenerator_smul, hq]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨symPow N g m, by beta_reduce; rw [hid, hq]⟩
  have hk : RingHom.ker ρ = (cyclicCoverIdeal N m σ).ideal V :=
    Scheme.IdealSheafData.ker_subschemeι_app _ V
  rw [← RingHom.comap_ker, hk, hspan]
  ext P
  simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
  exact map_dvd_iff Ψ

/-- Over every open `W ⊆ U`, the sections of `𝒜(L, m, s)` are uniquely `∑_{i<m} p^*(rᵢ) τⁱ`. -/
private theorem tau_basis (hm : 0 < m) (U : X.Opens) (t : N.val.obj (op U))
    (ht : ∀ (W : X.Opens) (hW : W ≤ U),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W) =>
        a • (N.val.map (homOfLE hW).op t : N.val.obj (op W)))
    (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op U))
    (hu : (cyclicCoverSituation N).algebraSheafIncl m U u =
      (cyclicCoverSituation N).algebraSheafIncl 1 U
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op U) t) ^ m)
    (f : Γ(X, U)) (hf : σ.val.app (op U) u = f) (W : X.Opens) (hW : W ≤ U) :
    Function.Bijective fun r : Fin m → Γ(X, W) =>
      ∑ i : Fin m, ((cyclicCoverToBase N m σ).app W).hom (r i) *
        cyclicCoverAlgebraIncl N m σ 1 W
          ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
            (N.val.map (homOfLE hW).op t)) ^ (i : ℕ) := by
  refine bijective_of_isBasis (ι := Fin m) X.sheaf
    ((TopCat.Sheaf.pushforward CommRingCat (cyclicCoverToBase N m σ).base).obj
      (cyclicCover N m σ).sheaf)
    _ X.isBasis_affineOpens U
    (fun W hW r => ∑ i : Fin m, ((cyclicCoverToBase N m σ).app W).hom (r i) *
        cyclicCoverAlgebraIncl N m σ 1 W
          ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
            (N.val.map (homOfLE hW).op t)) ^ (i : ℕ)) (fun W W' hW h r => ?_)
    (fun V hV hVU => ?_) W hW
  · change _ = ((cyclicCover N m σ).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom _
    refine Eq.trans ?_ (map_sum ((cyclicCover N m σ).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono _ h)).op).hom _ _).symm
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, tau_restrict N m σ U t hW h]
    exact congrArg (· * _) (ConcreteCategory.congr_hom
      (Scheme.Hom.naturality (cyclicCoverToBase N m σ) (homOfLE h).op) (r i))
  · obtain ⟨hs, hk⟩ := eval₂_of_isAffineOpen N m σ U t ht u hu f hf ⟨V, hV⟩ hVU
    have key := bijective_eval_sum_of_ker_eq_span hm _ _ hs hk
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at key
    exact key

end Geometry

/-- **The local equation of a cyclic cover.** If `t` is a basis of `N = L⁻¹` over an open `U` and
`f = σ(tᵐ)`, then over every open `W ⊆ U` the map `Γ(X, W)[T] ⟶ Γ(Z, p⁻¹ W)`, `T ↦ t`, of the
cyclic cover `p : Z ⟶ X` is surjective with kernel `(Tᵐ - f)`, and on every affine open `W ⊆ U` the
ideal of the zero scheme of `σ` is generated by `f`. -/
@[mmp "lem_km2c_ramified_cover_local_equation"]
public theorem cyclicCover_local_equation {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (m : ℕ) (hm : 0 < m)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (t : N.val.obj (op U))
    (ht : ∀ (W : X.Opens) (hW : W ≤ U),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W) =>
        a • (N.val.map (homOfLE hW).op t : N.val.obj (op W)))
    (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op U))
    (hu : (cyclicCoverSituation N).algebraSheafIncl m U u =
      (cyclicCoverSituation N).algebraSheafIncl 1 U
        ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op U) t) ^ m)
    (f : Γ(X, U)) (hf : σ.val.app (op U) u = f) :
    (∀ (W : X.Opens) (hW : W ≤ U),
      Function.Surjective (Polynomial.eval₂RingHom ((cyclicCoverToBase N m σ).app W).hom
          (cyclicCoverAlgebraIncl N m σ 1 W
            ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
              (N.val.map (homOfLE hW).op t)))) ∧
        RingHom.ker (Polynomial.eval₂RingHom ((cyclicCoverToBase N m σ).app W).hom
          (cyclicCoverAlgebraIncl N m σ 1 W
            ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
              (N.val.map (homOfLE hW).op t)))) =
          Ideal.span {Polynomial.X ^ m - Polynomial.C (X.presheaf.map (homOfLE hW).op f)}) ∧
    ∀ (W : X.affineOpens) (hW : W.1 ≤ U),
      (zeroSchemeIdeal N m σ).ideal W = Ideal.span {X.presheaf.map (homOfLE hW).op f} :=
  ⟨fun W hW => ker_eval₂RingHom_of_basis _ _ _ hm (tau_pow N m σ hm U t u hu f hf W hW)
      (tau_basis N m σ hm U t ht u hu f hf W hW),
    zeroSchemeIdeal_ideal_eq N m σ U t ht u hu f hf⟩

end LocalEquation

section Decomposition

variable {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (m : ℕ) (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf) (W : X.Opens)

/-- The ring map `𝒜_Sym(W) ⟶ Γ(Z, p⁻¹ W)`: the universal map of `Spec_X Sym(N)` followed by
restriction to the closed subscheme `Z`. -/
private noncomputable def inclRingHom :
    Stacks.RelativeSpec.AlgebraSheaf.sections (cyclicCoverSituation N).algebraSheaf W →+*
    Γ(cyclicCover N m σ, cyclicCoverToBase N m σ ⁻¹ᵁ W) :=
  ((Stacks.RelativeSpec.universalAlgebraMap
      (cyclicCoverSituation N).relativeSpecSituation).right.app (op W) ≫
    (cyclicCoverIdeal N m σ).subschemeι.app (symSpecToBase N ⁻¹ᵁ W)).hom

private theorem incl_eq (i : ℕ)
    (x : ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.obj (op W)) :
    cyclicCoverAlgebraIncl N m σ i W x =
      inclRingHom N m σ W ((cyclicCoverSituation N).algebraSheafIncl i W x) := rfl

private theorem base_eq (r : X.ringCatSheaf.obj.obj (op W)) :
    (cyclicCoverToBase N m σ).app W r =
      inclRingHom N m σ W (((cyclicCoverSituation N).algebraSheaf.hom.hom.app (op W)).hom r) := by
  unfold cyclicCoverToBase inclRingHom
  have h := Stacks.RelativeSpec.toBase_app (cyclicCoverSituation N).relativeSpecSituation W
  rw [Scheme.Hom.comp_app]
  change ((symSpecToBase N).app W ≫ _).hom r = _
  erw [h]
  rfl

private theorem algebraSheafIncl_add (i : ℤ)
    (x y : ((cyclicCoverSituation N).symmetricAlgebra.piece i).val.obj (op W)) :
    (cyclicCoverSituation N).algebraSheafIncl i W (x + y) =
      (cyclicCoverSituation N).algebraSheafIncl i W x +
        (cyclicCoverSituation N).algebraSheafIncl i W y := by
  unfold Stacks.LineBundle.Situation.algebraSheafIncl Stacks.RelativeSpec.ungradedAlgebraSheafIncl
  rw [(cyclicCoverSituation N).symmetricAlgebra.toPresheafGradedAlgebra.incl_add i x y]
  exact map_add _ _ _

private theorem cyclicCoverAlgebraIncl_add (i : ℕ)
    (x y : ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.obj (op W)) :
    cyclicCoverAlgebraIncl N m σ i W (x + y) =
      cyclicCoverAlgebraIncl N m σ i W x + cyclicCoverAlgebraIncl N m σ i W y := by
  rw [incl_eq, incl_eq, incl_eq, algebraSheafIncl_add, map_add]

private theorem cyclicCoverAlgebraIncl_smul (i : ℕ) (r : X.ringCatSheaf.obj.obj (op W))
    (x : ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.obj (op W)) :
    cyclicCoverAlgebraIncl N m σ i W (r • x) =
      (cyclicCoverToBase N m σ).app W r * cyclicCoverAlgebraIncl N m σ i W x := by
  rw [incl_eq, incl_eq, Stacks.LineBundle.Situation.algebraSheafIncl_smul, map_mul, base_eq]

private theorem cyclicCoverAlgebraIncl_mul (i j : ℕ)
    (a : ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.obj (op W))
    (b : ((cyclicCoverSituation N).symmetricAlgebra.piece (j : ℤ)).val.obj (op W)) :
    cyclicCoverAlgebraIncl N m σ i W a * cyclicCoverAlgebraIncl N m σ j W b =
      cyclicCoverAlgebraIncl N m σ (i + j) W
        ((eqToHom (congrArg (cyclicCoverSituation N).symmetricAlgebra.piece
            (Nat.cast_add i j).symm)).val.app (op W)
          (((cyclicCoverSituation N).symmetricAlgebra.mul i j).app (op W) a b)) := by
  rw [incl_eq, incl_eq, incl_eq, ← map_mul, Stacks.LineBundle.Situation.algebraSheafIncl_mul,
    incl_cast]
  exact (Nat.cast_add i j).symm

private theorem cyclicCoverAlgebraIncl_mul_reduce (k : ℕ)
    (c : ((cyclicCoverSituation N).symmetricAlgebra.piece (k : ℤ)).val.obj (op W))
    (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op W)) :
    cyclicCoverAlgebraIncl N m σ (k + m) W
        ((eqToHom (congrArg (cyclicCoverSituation N).symmetricAlgebra.piece
            (Nat.cast_add k m).symm)).val.app (op W)
          (((cyclicCoverSituation N).symmetricAlgebra.mul k m).app (op W) c u)) =
      (cyclicCoverToBase N m σ).app W (σ.val.app (op W) u) *
        cyclicCoverAlgebraIncl N m σ k W c := by
  rw [← cyclicCoverAlgebraIncl_mul, cyclicCoverAlgebraIncl_self, mul_comm]

/-- On sections of sheaves, a map that is injective over the members of a basis and compatible
with restriction is injective over every open. -/
private theorem injective_of_basis {X : TopCat.{u}} {ι : Type*}
    (F : ι → TopCat.Sheaf Ab.{u} X) (G : TopCat.Sheaf CommRingCat.{u} X)
    (Φ : ∀ W : Opens X, ((i : ι) → ToType ((F i).obj.obj (op W))) → ToType (G.obj.obj (op W)))
    (hΦ : ∀ {W W' : Opens X} (h : W' ⟶ W) x,
      Φ W' (fun i => (F i).obj.map h.op (x i)) = G.obj.map h.op (Φ W x))
    (B : Set (Opens X)) (hB : Opens.IsBasis B) (hinj : ∀ V ∈ B, Function.Injective (Φ V))
    (W : Opens X) : Function.Injective (Φ W) := by
  intro x y hxy
  choose V hVB hzV hVW using fun z : W => Opens.isBasis_iff_nbhd.mp hB z.2
  funext i
  refine TopCat.Sheaf.eq_of_locally_eq' (F i) V W (fun z => homOfLE (hVW z))
    (fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩) _ _ fun z => ?_
  exact congrFun (hinj (V z) (hVB z) (by rw [hΦ, hΦ, hxy] :
    Φ (V z) (fun i => (F i).obj.map (homOfLE (hVW z)).op (x i)) =
      Φ (V z) (fun i => (F i).obj.map (homOfLE (hVW z)).op (y i)))) i

/-- On sections of sheaves, a map that is bijective over the members of a basis and compatible
with restriction is bijective over every open. -/
private theorem bijective_of_basis {X : TopCat.{u}} {ι : Type*}
    (F : ι → TopCat.Sheaf Ab.{u} X) (G : TopCat.Sheaf CommRingCat.{u} X)
    (Φ : ∀ W : Opens X, ((i : ι) → ToType ((F i).obj.obj (op W))) → ToType (G.obj.obj (op W)))
    (hΦ : ∀ {W W' : Opens X} (h : W' ⟶ W) x,
      Φ W' (fun i => (F i).obj.map h.op (x i)) = G.obj.map h.op (Φ W x))
    (B : Set (Opens X)) (hB : Opens.IsBasis B) (hbij : ∀ V ∈ B, Function.Bijective (Φ V))
    (W : Opens X) : Function.Bijective (Φ W) := by
  have hinj := injective_of_basis F G Φ hΦ B hB (fun V hV => (hbij V hV).1)
  refine ⟨hinj W, fun g => ?_⟩
  choose V hVB hzV hVW using fun z : W => Opens.isBasis_iff_nbhd.mp hB z.2
  have hcov : W ≤ iSup V := fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩
  choose x hx using fun z => (hbij (V z) (hVB z)).2 (G.obj.map (homOfLE (hVW z)).op g)
  have hcompat : ∀ z z',
      (fun i => (F i).obj.map (homOfLE inf_le_left : V z ⊓ V z' ⟶ V z).op (x z i)) =
      (fun i => (F i).obj.map (homOfLE inf_le_right : V z ⊓ V z' ⟶ V z').op (x z' i)) := by
    intro z z'
    apply hinj
    rw [hΦ, hΦ, hx, hx, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← G.obj.map_comp, ← G.obj.map_comp]
    rfl
  have hglue := fun i => TopCat.Sheaf.existsUnique_gluing' (F i) V W (fun z => homOfLE (hVW z)) hcov
    (fun z => x z i) (fun z z' => congrFun (hcompat z z') i)
  choose s hs _ using hglue
  refine ⟨s, TopCat.Sheaf.eq_of_locally_eq' G V W (fun z => homOfLE (hVW z)) hcov _ _ fun z => ?_⟩
  rw [← hΦ, ← hx z]
  congr 1
  funext i
  exact hs i z

section Chart

open Polynomial PresheafOfModules Stacks.LineBundle

section PolynomialModel

variable (D : Stacks.LineBundle.Situation.{u})

/-- **A monomial of the polynomial model comes from a symmetric power.** -/
private theorem polynomialAlgEquiv_symm_monomial_mem (U : D.X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U.1) Γ(D.L, U.1)) (k : ℕ) (c : Γ(D.X, U.1)) :
    (D.polynomialAlgEquiv U b).symm (monomial k c) ∈
      SymPow.symmetricPower k Γ(D.X, U.1) Γ(D.L, U.1) := by
  have h : (D.polynomialAlgEquiv U b).symm (monomial k c) =
      c • (SymmetricAlgebra.ι Γ(D.X, U.1) Γ(D.L, U.1) (b PUnit.unit)) ^ k := by
    rw [AlgEquiv.symm_apply_eq, map_smul, map_pow, (polynomialAlgEquiv_ι D),
      Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
  rw [h]
  exact Submodule.smul_mem _ c
    (Submodule.pow_mem_pow _ (LinearMap.mem_range_self _ (b PUnit.unit)) k)

/-- **Over a trivializing affine open the homogeneous functions of degree `k` are the images of
the monomials `c Xᵏ` of the polynomial model.** -/
private theorem exists_totalFunction_iff (U : D.X.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(D.X, U.1) Γ(D.L, U.1)) (k : ℕ)
    (a : Γ(D.totalSpace, D.totalSpaceToBase ⁻¹ᵁ U.1)) :
    (∃ x, D.totalFunction k U.1 x = a) ↔
      ∃ c : Γ(D.X, U.1), D.polynomialSectionsRingEquiv U b (monomial k c) = a := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Stacks.SymAlgSections.pieceUnit D.L U.2 k).surjective x
    obtain ⟨c, hc⟩ := (polynomialAlgEquiv_mem_range_monomial D) U b k y.2
    refine ⟨c, ?_⟩
    rw [← (symSectionsRingEquiv_coe D)]
    change D.symSectionsRingEquiv U ((D.polynomialAlgEquiv U b).symm (monomial k c)) = _
    rw [show (monomial k c : Γ(D.X, U.1)[X]) = D.polynomialAlgEquiv U b y from hc,
      AlgEquiv.symm_apply_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨Stacks.SymAlgSections.pieceUnit D.L U.2 k
      ⟨_, (polynomialAlgEquiv_symm_monomial_mem D) U b k c⟩, ?_⟩
    rw [← (symSectionsRingEquiv_coe D)]
    rfl

end PolynomialModel

/-- Over an affine open `W` on which `N` is trivial, `∑ᵢ ιᵢ` is bijective: the polynomial model
`Γ(X, W)[T]/(Tᵐ - f)` of the local equation is free on `1, T, …, Tᵐ⁻¹`. -/
private theorem bijective_sum_of_isAffineOpen (hm : 0 < m) (hW : IsAffineOpen W)
    (e : N.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) :
    Function.Bijective
        (fun x : (i : Fin m) →
            ((cyclicCoverSituation N).symmetricAlgebra.piece ((i : ℕ) : ℤ)).val.obj (op W) =>
          ∑ i : Fin m, cyclicCoverAlgebraIncl N m σ (i : ℕ) W (x i)) := by
  set D := cyclicCoverSituation N with hD
  let U : D.X.affineOpens := ⟨W, hW⟩
  let t : N.val.obj (op W) := e.inv.val.app (op (Over.mk (𝟙 W))) (1 : X.ringCatSheaf.obj.obj (op W))
  have key : ∀ (W' : X.Opens) (hW : W' ≤ W) (a : X.ringCatSheaf.obj.obj (op W')),
      a • (N.val.map (homOfLE hW).op t : N.val.obj (op W')) =
        e.inv.val.app (op (Over.mk (homOfLE hW))) a := by
    intro W' hW a
    have h1 := PresheafOfModules.naturality_apply e.inv.val (X := op (Over.mk (𝟙 W)))
      (Y := op (Over.mk (homOfLE hW)))
      (Over.homMk (homOfLE hW) : Over.mk (homOfLE hW) ⟶ Over.mk (𝟙 W)).op
      (1 : X.ringCatSheaf.obj.obj (op W))
    erw [PresheafOfModules.unit_map_one] at h1
    have h2 := (e.inv.val.app (op (Over.mk (homOfLE hW)))).hom.map_smul a
      (1 : X.ringCatSheaf.obj.obj (op W'))
    exact (congrArg (fun z : N.val.obj (op W') => a • z) h1).symm.trans
      (h2.symm.trans (congrArg _ (mul_one a)))
  have ht : ∀ (W' : X.Opens) (hW : W' ≤ W),
      Function.Bijective fun a : X.ringCatSheaf.obj.obj (op W') =>
        a • (N.val.map (homOfLE hW).op t : N.val.obj (op W')) := by
    intro W' hW
    have : (fun a : X.ringCatSheaf.obj.obj (op W') =>
        a • (N.val.map (homOfLE hW).op t : N.val.obj (op W'))) =
          e.inv.val.app (op (Over.mk (homOfLE hW))) :=
      funext (key W' hW)
    rw [this]
    exact ((PresheafOfModules.toPresheaf _ ⋙
      (CategoryTheory.evaluation _ _).obj (op (Over.mk (homOfLE hW))) ⋙ forget _).mapIso
        ((SheafOfModules.forget _).mapIso e.symm)).toEquiv.bijective
  have htW : N.val.map (homOfLE (le_refl W)).op t = t := by
    simp <;> rfl
  have ht0 : Function.Bijective (LinearMap.toSpanSingleton Γ(X, W) Γ(N, W) t) := by
    have := ht W le_rfl
    rwa [htW] at this
  let b : Module.Basis PUnit.{u + 1} Γ(X, W) Γ(N, W) :=
    (Module.Basis.singleton PUnit.{u + 1} Γ(X, W)).map
      (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, W) Γ(N, W) t) ht0)
  have hb : b PUnit.unit = t := by
    simp [b]
    exact one_smul _ _
  let Ψ := D.polynomialSectionsRingEquiv U b
  have F1 : ∀ (k : ℕ) (x : (D.symmetricAlgebra.piece (k : ℤ)).val.obj (op W)),
      ∃ c, D.totalFunction k W x = Ψ (monomial k c) := fun k x => by
    obtain ⟨c, hc⟩ := (exists_totalFunction_iff D U b k _).1 ⟨x, rfl⟩
    exact ⟨c, hc.symm⟩
  have F3 : ∀ (k : ℕ) (c : Γ(X, W)), ∃ x : (D.symmetricAlgebra.piece (k : ℤ)).val.obj (op W),
      D.totalFunction k W x = Ψ (monomial k c) := fun k c =>
    (exists_totalFunction_iff D U b k _).2 ⟨c, rfl⟩
  have ΨX : Ψ Polynomial.X = D.totalFunction 1 W (D.symmetricAlgebraGen.val.app (op W) t) := by
    show D.symSectionsRingEquiv U ((D.polynomialAlgEquiv U b).symm Polynomial.X) = _
    have h : (D.polynomialAlgEquiv U b).symm Polynomial.X =
        SymmetricAlgebra.ι Γ(X, W) Γ(N, W) t := by
      rw [AlgEquiv.symm_apply_eq, ← hb]
      exact (polynomialAlgEquiv_ι D U b).symm
    rw [h]
    exact (symSectionsRingEquiv_coe D U 1
      (⟨SymmetricAlgebra.ι Γ(X, W) Γ(N, W) (show Γ(N, W) from t),
        SymPow.ι_mem_symmetricPowerInt_one _ _ _⟩ : SymPow.symmetricPower 1 Γ(X, W) Γ(N, W))).trans
      (congrArg (D.totalFunction 1 W) (pieceUnit_one_ι N hW t))
  have hu := incl_symPow N (D.symmetricAlgebraGen.val.app (op W) t) m
  have hloc := (cyclicCover_local_equation N m hm σ W t ht _ hu _ rfl).1 W le_rfl
  set ψ := Polynomial.eval₂RingHom ((cyclicCoverToBase N m σ).app W).hom
    (cyclicCoverAlgebraIncl N m σ 1 W
      ((cyclicCoverSituation N).symmetricAlgebraGen.val.app (op W)
        (N.val.map (homOfLE (le_refl W)).op t))) with hψ
  let ρ := ((cyclicCoverIdeal N m σ).subschemeι.app (symSpecToBase N ⁻¹ᵁ W)).hom
  have hρΨ : ∀ P, ρ (Ψ P) = ψ P := by
    intro P
    refine RingHom.congr_fun (Polynomial.ringHom_ext (f := ρ.comp Ψ.toRingHom) (g := ψ)
      (fun r => ?_) ?_) P
    · change ρ (Ψ (Polynomial.C r)) = ψ (Polynomial.C r)
      rw [D.polynomialSectionsRingEquiv_C U b r, hψ, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      unfold cyclicCoverToBase
      rw [Scheme.Hom.comp_app]
      rfl
    · change ρ (Ψ Polynomial.X) = ψ Polynomial.X
      rw [ΨX, hψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, htW]
      rfl
  have hsum : ∀ (d : Fin m → Γ(X, W)) (x : (i : Fin m) →
      ((cyclicCoverSituation N).symmetricAlgebra.piece ((i : ℕ) : ℤ)).val.obj (op W)),
      (∀ i : Fin m, D.totalFunction (i : ℕ) W (x i) = Ψ (monomial (i : ℕ) (d i))) →
      ∑ i : Fin m, cyclicCoverAlgebraIncl N m σ (i : ℕ) W (x i) =
        ψ (∑ i : Fin m, Polynomial.C (d i) * Polynomial.X ^ (i : ℕ)) := by
    intro d x hx
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.C_mul_X_pow_eq_monomial, ← hρΨ, ← hx i]
    rfl
  have hP := bijective_eval_sum_of_ker_eq_span hm _ ψ hloc.1 hloc.2
  choose c hc using F1
  refine ⟨fun x y hxy => funext fun j => totalFunction_injective D U j ?_, fun g => ?_⟩
  · have := hP.1 ((hsum _ x fun i => hc i (x i)).symm.trans
      (hxy.trans (hsum _ y fun i => hc i (y i))))
    rw [hc j (x j), hc j (y j), congrFun this j]
  · obtain ⟨d, rfl⟩ := hP.2 g
    choose x hx using fun i : Fin m => F3 i (d i)
    exact ⟨x, hsum d x hx⟩

end Chart

/-- The affine opens on which `N` is trivial form a basis of `X`. -/
private theorem isBasis_trivializing :
    Opens.IsBasis {V : X.Opens | IsAffineOpen V ∧
      Nonempty (N.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))} := by
  refine Opens.isBasis_iff_nbhd.mpr fun {W x} hx => ?_
  obtain ⟨U, hxU, ⟨e⟩⟩ := (cyclicCoverSituation N).exists_trivializing_affineOpen x
  obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ U.1 ⊓ W from ⟨hxU, hx⟩)
  exact ⟨V, ⟨hV, ⟨Stacks.SheafOfModules.isoUnitOverOfHom N (homOfLE (hVW.trans inf_le_left)) e⟩⟩,
    hxV, hVW.trans inf_le_right⟩

private theorem bijective_sum_cyclicCoverAlgebraIncl (hm : 0 < m) :
    Function.Bijective
        (fun x : (i : Fin m) →
            ((cyclicCoverSituation N).symmetricAlgebra.piece ((i : ℕ) : ℤ)).val.obj (op W) =>
          ∑ i : Fin m, cyclicCoverAlgebraIncl N m σ (i : ℕ) W (x i)) := by
  let F : Fin m → TopCat.Sheaf Ab.{u} X := fun i =>
    (SheafOfModules.toSheaf X.ringCatSheaf).obj
      ((cyclicCoverSituation N).symmetricAlgebra.piece ((i : ℕ) : ℤ))
  let G : TopCat.Sheaf CommRingCat.{u} X :=
    (TopCat.Sheaf.pushforward CommRingCat (cyclicCoverToBase N m σ).base).obj
      (cyclicCover N m σ).sheaf
  let Φ : ∀ W : X.Opens, ((i : Fin m) → ToType ((F i).obj.obj (op W))) →
      ToType (G.obj.obj (op W)) := fun W x =>
    (∑ i : Fin m, cyclicCoverAlgebraIncl N m σ (i : ℕ) W (x i) :
      Γ(cyclicCover N m σ, cyclicCoverToBase N m σ ⁻¹ᵁ W))
  have hΦ : ∀ {W W' : X.Opens} (h : W' ⟶ W) x,
      Φ W' (fun i => (F i).obj.map h.op (x i)) = G.obj.map h.op (Φ W x) := by
    intro W W' h x
    change (∑ i : Fin m, cyclicCoverAlgebraIncl N m σ (i : ℕ) W'
        (((cyclicCoverSituation N).symmetricAlgebra.piece ((i : ℕ) : ℤ)).val.map
          (homOfLE h.le).op (x i)) : Γ(cyclicCover N m σ, cyclicCoverToBase N m σ ⁻¹ᵁ W')) =
      ((cyclicCover N m σ).presheaf.map
        (homOfLE ((cyclicCoverToBase N m σ).preimage_mono h.le)).op).hom
        (∑ i : Fin m, cyclicCoverAlgebraIncl N m σ (i : ℕ) W (x i))
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact incl_nat N m σ (i : ℕ) W W' h.le (x i)
  have hbij : ∀ V ∈ {V : X.Opens | IsAffineOpen V ∧
      Nonempty (N.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))},
      Function.Bijective (Φ V) := fun V ⟨hV, ⟨e⟩⟩ =>
    bijective_sum_of_isAffineOpen N m σ V hm hV e
  exact bijective_of_basis F G Φ hΦ _ (isBasis_trivializing N) hbij W

/-- **Decomposition of the cyclic cover algebra.** For `0 < m`, over every open `W ⊆ X` the
map `(xᵢ)_{i<m} ↦ ∑ᵢ ιᵢ(xᵢ)` from `∏_{i<m} Γ(W, Symⁱ N)` to the sections of `𝒜(L, m, s)` is
bijective, and each `ιᵢ` is `𝒪_X(W)`-linear; moreover `ιᵢ(a) ιⱼ(b) = ι_{i+j}(ab)`, and
`ι_{k+m}(c u) = σ(u) ι_k(c)` for `c ∈ Symᵏ(N)`, `u ∈ Symᵐ(N)`. -/
@[mmp "lem_km2c_cyclic_cover_algebra_decomposition"]
public theorem cyclicCoverAlgebra_decomposition {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (m : ℕ) (hm : 0 < m)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf) (W : X.Opens) :
    Function.Bijective
        (fun x : (i : Fin m) →
            ((cyclicCoverSituation N).symmetricAlgebra.piece ((i : ℕ) : ℤ)).val.obj (op W) =>
          ∑ i : Fin m, cyclicCoverAlgebraIncl N m σ (i : ℕ) W (x i)) ∧
      (∀ (i : ℕ) (x y : ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.obj (op W)),
        cyclicCoverAlgebraIncl N m σ i W (x + y) =
          cyclicCoverAlgebraIncl N m σ i W x + cyclicCoverAlgebraIncl N m σ i W y) ∧
      (∀ (i : ℕ) (r : X.ringCatSheaf.obj.obj (op W))
          (x : ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.obj (op W)),
        cyclicCoverAlgebraIncl N m σ i W (r • x) =
          (cyclicCoverToBase N m σ).app W r * cyclicCoverAlgebraIncl N m σ i W x) ∧
      (∀ (i j : ℕ) (a : ((cyclicCoverSituation N).symmetricAlgebra.piece (i : ℤ)).val.obj (op W))
          (b : ((cyclicCoverSituation N).symmetricAlgebra.piece (j : ℤ)).val.obj (op W)),
        cyclicCoverAlgebraIncl N m σ i W a * cyclicCoverAlgebraIncl N m σ j W b =
          cyclicCoverAlgebraIncl N m σ (i + j) W
            ((eqToHom (congrArg (cyclicCoverSituation N).symmetricAlgebra.piece
                (Nat.cast_add i j).symm)).val.app (op W)
              (((cyclicCoverSituation N).symmetricAlgebra.mul i j).app (op W) a b))) ∧
      (∀ (k : ℕ) (c : ((cyclicCoverSituation N).symmetricAlgebra.piece (k : ℤ)).val.obj (op W))
          (u : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op W)),
        cyclicCoverAlgebraIncl N m σ (k + m) W
            ((eqToHom (congrArg (cyclicCoverSituation N).symmetricAlgebra.piece
                (Nat.cast_add k m).symm)).val.app (op W)
              (((cyclicCoverSituation N).symmetricAlgebra.mul k m).app (op W) c u)) =
          (cyclicCoverToBase N m σ).app W (σ.val.app (op W) u) *
            cyclicCoverAlgebraIncl N m σ k W c) :=
  ⟨bijective_sum_cyclicCoverAlgebraIncl N m σ W hm, cyclicCoverAlgebraIncl_add N m σ W,
    cyclicCoverAlgebraIncl_smul N m σ W,
    cyclicCoverAlgebraIncl_mul N m σ W, cyclicCoverAlgebraIncl_mul_reduce N m σ W⟩

end Decomposition

section Unramified

open Polynomial

/-- `Tᵐ - g` is monic once `m` is invertible. -/
private theorem monic_X_pow_sub_C_of_isUnit {R : Type*} [CommRing R] {m : ℕ}
    (hm : IsUnit (m : R)) (g : R) : (Polynomial.X ^ m - C g).Monic := by
  rcases eq_or_ne m 0 with rfl | hm0
  · have : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using hm)
    exact Subsingleton.elim _ _
  · exact monic_X_pow_sub_C g hm0

/-- For `m` invertible in `R` and `v` a unit, `R[T]/(Tᵐ - v)` is étale over `R`. -/
private theorem etale_adjoinRoot_X_pow_sub_C {R : Type*} [CommRing R] {m : ℕ}
    (hm : IsUnit (m : R)) (v : Rˣ) :
    Algebra.Etale R (AdjoinRoot (Polynomial.X ^ m - C (v : R))) := by
  let P : StandardEtalePair R :=
    { f := Polynomial.X ^ m - C (v : R), monic_f := monic_X_pow_sub_C_of_isUnit hm _, g := 1
      cond := by
        obtain ⟨a, b, h⟩ := separable_X_pow_sub_C_unit v hm
        exact ⟨b, a, 1, by rw [pow_one, ← h]; ring⟩ }
  have h1 : IsUnit (AdjoinRoot.mk P.f P.g) := by simp [P]
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (AdjoinRoot P.f) (Localization.Away (AdjoinRoot.mk P.f P.g))
      _ h1).symm.restrictScalars R))

/-- The basis `1, T, …, Tᵐ⁻¹` of `R[T]/(Tᵐ - g)` over `R`, for `m` invertible in `R`; over the
zero ring, where `m = 0` is allowed, any `Fin m`-indexed family is a basis. -/
private noncomputable def adjoinRootBasis {R : Type*} [CommRing R] {m : ℕ}
    (hm : IsUnit (m : R)) (g : R) :
    Module.Basis (Fin m) R (AdjoinRoot (Polynomial.X ^ m - C g)) := by
  by_cases hR : Nontrivial R
  · have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    let pb := AdjoinRoot.powerBasis' (monic_X_pow_sub_C_of_isUnit hm g)
    exact pb.basis.reindex (finCongr (by simp [pb, natDegree_X_pow_sub_C]))
  · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    have : Subsingleton (AdjoinRoot (Polynomial.X ^ m - C g)) := Module.subsingleton R _
    exact .ofRepr (LinearEquiv.ofSubsingleton _ _)

/-- **The local model of an unramified cyclic cover.** If `ψ : R[T] → A` is surjective with
kernel `(Tᵐ - v)`, for a unit `v` and `m` invertible in `R`, then `R → A` is finite étale and
makes `A` free of rank `m`. -/
private theorem etale_finite_isFiniteLocallyFreeOfRank_of_ker {R A : Type u} [CommRing R]
    [CommRing A] (ψ : Polynomial R →+* A) (hs : Function.Surjective ψ) {m : ℕ} {v : Rˣ}
    (hk : RingHom.ker ψ = Ideal.span {Polynomial.X ^ m - C (v : R)}) (hm : IsUnit (m : R)) :
    (ψ.comp C).Etale ∧ (ψ.comp C).Finite ∧
      letI := (ψ.comp C).toAlgebra
      Module.IsFiniteLocallyFreeOfRank R A m := by
  letI := (ψ.comp C).toAlgebra
  let e : AdjoinRoot (Polynomial.X ^ m - C (v : R)) ≃ₐ[R] A := AlgEquiv.ofRingEquiv
    (f := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs))
    fun _ => rfl
  have := etale_adjoinRoot_X_pow_sub_C hm v
  have := (monic_X_pow_sub_C_of_isUnit hm (v : R)).finite_adjoinRoot
  exact ⟨RingHom.etale_algebraMap.mpr (Algebra.Etale.of_equiv e),
    RingHom.finite_algebraMap.mpr (Module.Finite.equiv e.toLinearEquiv),
    Module.isFiniteLocallyFreeOfRank_of_basis ((adjoinRootBasis hm (v : R)).map e.toLinearEquiv)⟩

section Chart

variable {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (U : X.affineOpens) (b : Module.Basis PUnit.{u + 1} Γ(X, U.1) Γ(N, U.1))

/-- The section `tᵐ` of `Symᵐ N` over `U`, for the basis `t` of `Γ(N, U)`. -/
private noncomputable def basisPow (m : ℕ) :
    ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op U.1) :=
  Stacks.SymAlgSections.pieceUnit N U.2 m
    ⟨(SymmetricAlgebra.ι Γ(X, U.1) Γ(N, U.1) (b PUnit.unit)) ^ m,
      Submodule.pow_mem_pow _ (LinearMap.mem_range_self _ _) m⟩

private theorem exists_eq_smul_basisPow (m : ℕ)
    (x : ((cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ)).val.obj (op U.1)) :
    ∃ c : Γ(X, U.1), x = id (α := X.ringCatSheaf.obj.obj (op U.1)) c • basisPow N U b m := by
  obtain ⟨y, rfl⟩ := (Stacks.SymAlgSections.pieceUnit N U.2 m).surjective x
  obtain ⟨c, hc⟩ := polynomialAlgEquiv_mem_range_monomial (cyclicCoverSituation N) U b m y.2
  refine ⟨c, ?_⟩
  have hy : y = c • ⟨(SymmetricAlgebra.ι Γ(X, U.1) Γ(N, U.1) (b PUnit.unit)) ^ m,
      Submodule.pow_mem_pow _ (LinearMap.mem_range_self _ _) m⟩ := by
    apply Subtype.ext
    have : ((cyclicCoverSituation N).polynomialAlgEquiv U b).symm (monomial m c) = (y : _) := by
      rw [AlgEquiv.symm_apply_eq]; exact hc
    rw [← this, AlgEquiv.symm_apply_eq, Submodule.coe_smul, map_smul, map_pow,
      polynomialAlgEquiv_ι (cyclicCoverSituation N) U b, Polynomial.smul_eq_C_mul,
      C_mul_X_pow_eq_monomial]
  rw [hy]
  exact (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj) (PresheafOfModules.symPowInt (m : ℤ) N.val)) (op U.1)).hom.map_smul c _

private theorem symSpecFunction_basisPow (m : ℕ) :
    symSpecFunction N m U.1 (basisPow N U b m) =
      (cyclicCoverSituation N).polynomialSectionsRingEquiv U b (Polynomial.X ^ m) := by
  refine (symSectionsRingEquiv_coe (cyclicCoverSituation N) U m _).symm.trans ?_
  change _ = (cyclicCoverSituation N).symSectionsRingEquiv U
    (((cyclicCoverSituation N).polynomialAlgEquiv U b).symm (Polynomial.X ^ m))
  congr 1
  rw [eq_comm, AlgEquiv.symm_apply_eq]
  simp [polynomialAlgEquiv_ι (cyclicCoverSituation N) U b]

/-- The coefficient `σ(tᵐ)` of the local equation `Tᵐ - σ(tᵐ)`. -/
private noncomputable def chartCoeff (m : ℕ)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf) : Γ(X, U.1) :=
  σ.val.app (op U.1) (basisPow N U b m)

private theorem isUnit_chartCoeff (m : ℕ)
    (ψ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ≅
      SheafOfModules.unit X.ringCatSheaf) :
    IsUnit (chartCoeff N U b m ψ.hom) := by
  obtain ⟨c, hc⟩ := exists_eq_smul_basisPow N U b m
    (ψ.inv.val.app (op U.1) (1 : X.ringCatSheaf.obj.obj (op U.1)))
  have h2 := congrArg (fun χ => χ.val.app (op U.1) (1 : X.ringCatSheaf.obj.obj (op U.1)))
    ψ.inv_hom_id
  have h3 : (show Γ(X, U.1) from ψ.hom.val.app (op U.1)
      (ψ.inv.val.app (op U.1) (1 : X.ringCatSheaf.obj.obj (op U.1)))) = 1 := h2
  rw [hc, (ψ.hom.val.app (op U.1)).hom.map_smul] at h3
  exact IsUnit.of_mul_eq_one_right _ h3

private theorem cyclicCoverGenerator_basisPow (m : ℕ)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    cyclicCoverGenerator N m σ U.1 (basisPow N U b m) =
      (cyclicCoverSituation N).polynomialSectionsRingEquiv U b
        (Polynomial.X ^ m - C (chartCoeff N U b m σ)) := by
  rw [map_sub, (cyclicCoverSituation N).polynomialSectionsRingEquiv_C, cyclicCoverGenerator,
    symSpecFunction_basisPow]
  rfl

/-- The presentation `Γ(X, U)[T] → Γ(p⁻¹U)` of the functions on the cover over `U`, sending `T`
to the fibre coordinate of the basis `t`. -/
private noncomputable def chartPresentation (m : ℕ)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    Polynomial Γ(X, U.1) →+*
      Γ(cyclicCover N m σ, (cyclicCoverIdeal N m σ).subschemeι ⁻¹ᵁ symSpecToBase N ⁻¹ᵁ U.1) :=
  ((cyclicCoverIdeal N m σ).subschemeι.app (symSpecToBase N ⁻¹ᵁ U.1)).hom.comp
    ((cyclicCoverSituation N).polynomialSectionsRingEquiv U b).toRingHom

private theorem chartPresentation_comp_C (m : ℕ)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (chartPresentation N U b m σ).comp C = ((cyclicCoverToBase N m σ).app U.1).hom := by
  ext r
  change ((cyclicCoverIdeal N m σ).subschemeι.app _).hom
    ((cyclicCoverSituation N).polynomialSectionsRingEquiv U b (C r)) = _
  rw [(cyclicCoverSituation N).polynomialSectionsRingEquiv_C]
  unfold cyclicCoverToBase
  rw [Scheme.Hom.comp_app]
  rfl

private theorem chartPresentation_surjective (m : ℕ)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    Function.Surjective (chartPresentation N U b m σ) :=
  ((cyclicCoverIdeal N m σ).subschemeι_app_surjective ⟨_, U.2.preimage (symSpecToBase N)⟩).comp
    ((cyclicCoverSituation N).polynomialSectionsRingEquiv U b).surjective

private theorem ker_chartPresentation (m : ℕ)
    (σ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    RingHom.ker (chartPresentation N U b m σ) =
      Ideal.span {Polynomial.X ^ m - C (chartCoeff N U b m σ)} := by
  unfold chartPresentation
  set e := (cyclicCoverSituation N).polynomialSectionsRingEquiv U b
  have hgen : ∀ x, cyclicCoverGenerator N m σ U.1 x ∈
      Ideal.map e.toRingHom (Ideal.span {Polynomial.X ^ m - C (chartCoeff N U b m σ)}) := by
    intro x
    obtain ⟨c, rfl⟩ := exists_eq_smul_basisPow N U b m x
    rw [cyclicCoverGenerator_smul, cyclicCoverGenerator_basisPow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span rfl))
  apply le_antisymm
  · intro P hP
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker,
      Scheme.IdealSheafData.ker_subschemeι_app (I := cyclicCoverIdeal N m σ)
        ⟨_, U.2.preimage (symSpecToBase N)⟩,
      ideal_cyclicCoverIdeal N m σ U ⟨_, U.2.preimage (symSpecToBase N)⟩ le_rfl] at hP
    have hP' : e.toRingHom P ∈
        Ideal.map e.toRingHom (Ideal.span {Polynomial.X ^ m - C (chartCoeff N U b m σ)}) := by
      refine (Ideal.span_le.mpr ?_) hP
      rintro _ ⟨x, rfl⟩
      simpa using hgen x
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).mp hP'
    rwa [e.injective hQP] at hQ
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      RingHom.comp_apply]
    change (cyclicCoverIdeal N m σ).subschemeι.app (symSpecToBase N ⁻¹ᵁ U.1) (e _) = 0
    rw [← cyclicCoverGenerator_basisPow]
    exact subschemeι_app_cyclicCoverGenerator N m σ U.1 _

include b in
/-- Over a trivialising affine open `U`, the ring map `Γ(X, U) → Γ(p⁻¹U)` of the cover is finite
étale, making `Γ(p⁻¹U)` locally free of rank `m`. -/
private theorem etale_finite_isFiniteLocallyFreeOfRank_app (m : ℕ) (hm : IsUnit (m : Γ(X, ⊤)))
    (ψ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ≅
      SheafOfModules.unit X.ringCatSheaf) :
    ((cyclicCoverToBase N m ψ.hom).app U.1).hom.Etale ∧
      ((cyclicCoverToBase N m ψ.hom).app U.1).hom.Finite ∧
      letI := ((cyclicCoverToBase N m ψ.hom).app U.1).hom.toAlgebra
      Module.IsFiniteLocallyFreeOfRank Γ(X, U.1)
        Γ(cyclicCover N m ψ.hom, cyclicCoverToBase N m ψ.hom ⁻¹ᵁ U.1) m := by
  rw [← chartPresentation_comp_C N U b]
  exact etale_finite_isFiniteLocallyFreeOfRank_of_ker _ (chartPresentation_surjective N U b m _)
    (v := (isUnit_chartCoeff N U b m ψ).unit) (ker_chartPresentation N U b m ψ.hom)
    (by simpa using hm.map (X.presheaf.map (homOfLE le_top : U.1 ⟶ ⊤).op).hom)

end Chart

/-- A property of the ring map `f.app U` passes to the global sections of the restriction
`f ∣_ U`. -/
private theorem appTop_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (h : P (f.app U).hom) : P ((f ∣_ U).appTop).hom := by
  have key : ∀ (A : Y.Opens) (B : X.Opens) (e : B ≤ f ⁻¹ᵁ A), A = U → B = f ⁻¹ᵁ U →
      P (f.appLE A B e).hom := by
    rintro A B e rfl rfl
    rwa [← Scheme.Hom.app_eq_appLE]
  rw [Scheme.Hom.appTop, morphismRestrict_app']
  exact key _ _ _ U.ι_image_top (f ⁻¹ᵁ U).ι_image_top

/-- **Unramified cyclic covers are finite étale of degree `m`.** If `m` is invertible on `X`
and `ψ : L⁻ᵐ ≅ 𝒪_X`, the unramified cyclic cover `p : X_{m,L} ⟶ X` is finite and étale, and
`p_* 𝒪_{X_{m,L}}` is locally free of rank `m`. -/
@[mmp "lem_km2c_unramified_cyclic_cover_etale"]
public theorem unramifiedCyclicCover_etale {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (m : ℕ) (hm : IsUnit (m : Γ(X, ⊤)))
    (ψ : (cyclicCoverSituation N).symmetricAlgebra.piece (m : ℤ) ≅
      SheafOfModules.unit X.ringCatSheaf) :
    IsFinite (unramifiedCyclicCover N m ψ) ∧ Etale (unramifiedCyclicCover N m ψ) ∧
      MMP.Intersection.Scheme.Modules.IsLocallyFreeOfRank
        ((Scheme.Modules.pushforward (unramifiedCyclicCover N m ψ)).obj
          (SheafOfModules.unit (cyclicCover N m ψ.hom).ringCatSheaf)) m := by
  let T := {U : X.affineOpens // Nonempty (Module.Basis PUnit.{u + 1} Γ(X, U.1) Γ(N, U.1))}
  have hT : ⨆ U : T, (U.1 : X.affineOpens).1 = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨U, ⟨hU, -, hb⟩, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
      (cyclicCoverSituation N).isBasis_chartOpens (show x ∈ (⊤ : X.Opens) from trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hb⟩, hxU⟩
  haveI : IsAffineHom (symSpecToBase N) := Stacks.RelativeSpec.isAffineHom_toBase _
  haveI : IsAffineHom (unramifiedCyclicCover N m ψ) := by
    unfold unramifiedCyclicCover cyclicCoverToBase; infer_instance
  haveI := Stacks.Morphisms.isFinite_isZariskiLocalAtTarget.{u}
  haveI := Stacks.Morphisms.isFinite_respectsIso.{u}
  haveI : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  suffices IsFinite (unramifiedCyclicCover N m ψ) ∧ Etale (unramifiedCyclicCover N m ψ) ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (unramifiedCyclicCover N m ψ) m by
    refine ⟨this.1, this.2.1, fun x => ?_⟩
    obtain ⟨V, hxV, ⟨e⟩⟩ :=
      ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_pointwise _ m).mp this.2.2).2 x
    exact ⟨V, hxV, ⟨e⟩⟩
  refine ⟨(IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _ hT).2 fun U => ?_,
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Etale) _ hT).2 fun U => ?_,
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property m) _ hT).2 fun U => ?_⟩ <;>
  obtain ⟨U, ⟨b⟩⟩ := U <;>
  haveI : IsAffine (unramifiedCyclicCover N m ψ ⁻¹ᵁ U.1).toScheme := U.2.preimage _ <;>
  haveI : IsAffine U.1.toScheme := U.2 <;>
  have h := etale_finite_isFiniteLocallyFreeOfRank_app N U b m hm ψ
  · rw [MorphismProperty.arrow_mk_iso_iff @IsFinite (arrowIsoSpecΓOfIsAffine _),
      IsFinite.SpecMap_iff]
    exact appTop_morphismRestrict _ _ _ h.2.1
  · exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).2 (appTop_morphismRestrict _ _ _ h.1)
  · letI := ((unramifiedCyclicCover N m ψ ∣_ U.1).appTop).hom.toAlgebra
    change Stacks.Morphisms.IsFiniteLocallyFreeOfRank _ m
    rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine _ m rfl]
    exact appTop_morphismRestrict _ _
      (fun {R S} [CommRing R] [CommRing S] (φ : R →+* S) =>
        letI := φ.toAlgebra; Module.IsFiniteLocallyFreeOfRank R S m) h.2.2

end Unramified

section LocallyFreeLocus

/-- A module isomorphic to a free module is locally free. -/
private theorem isLocallyFree_of_iso_free {Y : Scheme.{u}} {N : Y.Modules} {I : Type u}
    (e : N ≅ SheafOfModules.free I) : N.IsLocallyFree := fun _ => by
  let F := Scheme.Modules.restrictFunctor (⊤ : Y.Opens).ι
  haveI : Limits.PreservesColimitsOfShape.{u, u} (Discrete I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  exact ⟨⊤, trivial, I, ⟨F.mapIso e ≪≫
    (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I this
      (Scheme.Modules.restrictUnitIso (⊤ : Y.Opens).ι).symm).symm⟩⟩

/-- A trivialisation of `M` on the slice site over `U` makes the restriction of `M` to the open
subscheme `U` locally free. -/
private theorem isLocallyFree_restrict_of_over_iso_free {X : Scheme.{u}} {M : X.Modules}
    {U : X.Opens} {I : Type u} (e : M.over U ≅ SheafOfModules.free I) :
    ((Scheme.Modules.restrictFunctor U.ι).obj M).IsLocallyFree := by
  let F := (Scheme.Modules.overEquiv U).functor
  haveI : Limits.PreservesColimitsOfShape.{u, u} (Discrete I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  exact isLocallyFree_of_iso_free (((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    F.mapIso e ≪≫
    (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I this
      (Stacks.AlgebraicGeometry.CoherentFinite.overFunctorUnitIso U)).symm)

open Stacks.AlgebraicGeometry.ReflexiveModules in
/-- On an integral scheme, the stalks of a torsion free module are torsion free. -/
private theorem eq_zero_or_eq_zero_of_smul_eq_zero_stalk {X : Scheme.{u}} [IsIntegral X]
    {L : X.Modules} (htf : IsTorsionFree L) {x : X} {r : X.presheaf.stalk x}
    {m : L.presheaf.stalk x}
    (h : r • m = 0) : r = 0 ∨ m = 0 := by
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  obtain ⟨U, hxU, s, rfl⟩ := L.presheaf.exists_germ_eq m
  obtain ⟨W, hWU, hxW, a, ha, has⟩ :=
    exists_annihilator_of_isTorsionSection hxU ⟨r, hr, h⟩
  have ha0 : a ≠ 0 := fun h0 => ha (by rw [h0, map_zero])
  have hs : L.presheaf.map (homOfLE hWU).op s = 0 := by
    refine htf W _ fun y hy => ⟨X.presheaf.germ W y hy a, ?_, ?_⟩
    · intro h0
      exact ha0 (germ_injective_of_isIntegral X y hy (by rw [h0, map_zero]))
    · refine (L.val.germ_smul y W hy a _).symm.trans ?_
      erw [has, map_zero]
      rfl
  rw [← L.presheaf.germ_res_apply (homOfLE hWU) x hxW, hs, map_zero]

open Stacks.AlgebraicGeometry.ReflexiveModules in
/-- At a point of codimension at most one of a normal locally Noetherian integral scheme, the
stalk of a coherent torsion free module is free. -/
private theorem free_stalk_of_coheight_le_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {x : X} [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hx : Order.coheight x ≤ 1) (L : X.Modules) [SheafOfModules.IsCoherent L]
    (htf : IsTorsionFree L) : Module.Free (X.presheaf.stalk x) (L.presheaf.stalk x) := by
  haveI := krullDimLE_of_coheight_le (n := 1) (by exact_mod_cast hx)
  haveI : Ring.DimensionLEOne (X.presheaf.stalk x) :=
    ⟨fun hp0 hp => (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp ‹_›) _ hp0 hp⟩
  haveI : IsDedekindDomain (X.presheaf.stalk x) := {}
  haveI := Scheme.Modules.finite_stalk_of_isCoherent L x
  haveI : Module.IsTorsionFree (X.presheaf.stalk x) (L.presheaf.stalk x) :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr fun _ _ h =>
      eq_zero_or_eq_zero_of_smul_eq_zero_stalk htf h
  exact Module.free_of_finite_type_torsion_free'

/-- **The locally free locus of a rank one torsion free coherent sheaf on a normal variety has
complement of codimension at least two**: every point outside `locallyFreeLocus L` has
codimension at least two. -/
@[mmp "lem_km2c_locally_free_locus_codim_two"]
public theorem two_le_coheight_of_notMem_locallyFreeLocus {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} (hX : IsNormalVariety k f) (L : X.Modules)
    (hcoh : Stacks.SheafOfModules.IsCoherent L)
    (htf : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree L)
    (hrank : haveI : IsIntegral X := hX.1.toIsIntegral
      Scheme.Modules.fiberRank L (genericPoint X) = 1)
    {x : X} (hx : x ∉ locallyFreeLocus L) :
    2 ≤ Order.coheight x := by
  obtain ⟨hV, hN⟩ := hX
  haveI : AlgebraicGeometry.IsVariety k f := hV
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsIntegrallyClosed (X.presheaf.stalk x) := hN.stalk_normal x
  haveI : SheafOfModules.IsCoherent L :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_of_stacks hcoh
  haveI : L.IsFinitePresentation :=
    (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isFinitePresentation L).mp ‹_›
  haveI := Scheme.Modules.finite_stalk_of_isCoherent L x
  by_contra hlt
  haveI := free_stalk_of_coheight_le_one (by simpa using not_le.mp hlt) L htf
  obtain ⟨U, hxU, ⟨e⟩⟩ := Stacks.StalkFiniteType.exists_over_iso_free_of_stalk_basis L x
    (Module.Free.chooseBasis (X.presheaf.stalk x) (L.presheaf.stalk x))
  exact hx (le_locallyFreeLocus L (isLocallyFree_restrict_of_over_iso_free e) hxU)

end LocallyFreeLocus

section ContractedCurve

/-- A morphism is injective on the preimage of its biregular locus. -/
private lemma injOn_preimage_biregularLocus {X Y : Scheme} (f : X ⟶ Y) :
    Set.InjOn f.base (f ⁻¹ᵁ biregularLocus f : Set X) := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  have hinj : Function.Injective ((f ⁻¹ᵁ biregularLocus f).ι ≫ f).base := by
    rw [← morphismRestrict_ι]
    exact ((f ∣_ biregularLocus f) ≫ (biregularLocus f).ι).isOpenEmbedding.injective
  exact fun a ha b hb hab ↦ congrArg Subtype.val (@hinj ⟨a, ha⟩ ⟨b, hb⟩ hab)

/-- If `f : X ⟶ Y` is a birational morphism of varieties over `k` and `C ⊆ X` is an irreducible
closed curve with `f(C)` a point, then `C ⊆ Ex(f)`. -/
@[mmp "lem_km3c_contracted_curve_in_exceptional_set"]
public theorem subset_exceptionalSet_of_subsingleton_image {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsVariety k sX) (hY : IsVariety k sY) {f : X ⟶ Y} (hf : f ≫ sY = sX)
    (hbir : IsBirationalMorphism f) {C : Set X} (hCc : IsClosed C) (hCi : IsIrreducible C)
    (hCd : topologicalKrullDim C = 1) (hfC : (f.base '' C).Subsingleton) :
    C ⊆ (exceptionalSet f : Set X) := by
  intro x hx (hxV : f x ∈ biregularLocus f)
  -- `f(C) = {f x} ⊆ V_f`, so `f` is injective on `C`, so `C` is a point.
  have hCV : C ⊆ (f ⁻¹ᵁ biregularLocus f : Set X) := fun y hy ↦
    show f y ∈ biregularLocus f from hfC ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩ ▸ hxV
  have : Subsingleton C := Set.Subsingleton.coe_sort fun a ha b hb ↦
    injOn_preimage_biregularLocus f (hCV ha) (hCV hb) (hfC ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  have : DiscreteTopology C := ⟨Subsingleton.elim _ _⟩
  exact absurd (hCd ▸ topologicalKrullDim_zero_of_discreteTopology C) (by decide)

end ContractedCurve

end MMP.Mori

namespace MMP.Positivity

open MMP.Mori

/-- The coefficient of the crepant boundary along a non-exceptional prime divisor is the
coefficient of the boundary along the corresponding prime divisor of `X`. -/
private theorem exists_coeff_eq_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) {Y : Scheme.{u}} {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) (F : MMP.Mori.PrimeDivisor Y)
    (hE : ¬ RationalMap.IsExceptional (X := Y) f.toRationalMap F) :
    ∃ P : MMP.Mori.PrimeDivisor X, ΔY.coeff F = Δ.coeff P := by
  set D : DivisorOver k sX := ⟨Y, f, hY, hf, F⟩
  obtain ⟨P, hv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hklt.1.1 D hE
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hmτ⟩ := hΔY F
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
      hK.topologicalKrullDim_eq hv τ,
    DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P τ] at hmτ
  have hPU : (P.support ∩ (U : Set X)).Nonempty := by
    have hx : D.f D.E.genericPoint = P.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
    refine ⟨P.genericPoint, ?_, hx ▸ hU⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  refine ⟨P, neg_inj.mp (mul_left_cancel₀ (by positivity : (m : ℚ) ≠ 0) ?_)⟩
  linear_combination hmτ + hτ.2 P hPU

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- **The round-up of minus the crepant boundary of a klt pair is effective and exceptional.**
Let `(X, Δ)` be a klt pair with `Δ` effective, `g : Y ⟶ X` a proper birational morphism from a
normal variety and `Δ_Y` the crepant boundary of `(X, Δ)` on `Y`. Then `⌈-Δ_Y⌉` is effective,
and every prime divisor of `Y` with nonzero coefficient in `⌈-Δ_Y⌉` is `g`-exceptional. -/
@[mmp "lem_km3a_discrepancy_roundup_effective_exceptional"]
public theorem IsKltPair.isEffective_roundUp_neg_of_isCrepantBoundary {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {Y : Scheme.{u}}
    {g : Y ⟶ X} [IsProper g] (hY : IsNormalVariety k (g ≫ sX)) (hg : IsBirationalMorphism g)
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ g hY hg ΔY) :
    (-ΔY).roundUp.IsEffective ∧
      ∀ F : Mori.PrimeDivisor Y, (-ΔY).roundUp.coeff F ≠ 0 →
        RationalMap.IsExceptional (X := Y) g.toRationalMap F := by
  have hlt := MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary hklt hY hg hΔY
  refine ⟨fun F => ?_, fun F hF => ?_⟩
  · change (0 : ℤ) ≤ (-ΔY).roundUp.coeff F
    rw [DivisorWithCoeffs.coeff_roundUp, Int.le_ceil_iff]
    change ((0 : ℤ) : ℚ) - 1 < -ΔY.coeff F
    push_cast
    linarith [hlt F]
  · by_contra hE
    obtain ⟨P, hP⟩ := exists_coeff_eq_of_not_isExceptional hklt hY hg hΔY F hE
    refine hF ?_
    rw [DivisorWithCoeffs.coeff_roundUp, Int.ceil_eq_iff]
    change ((0 : ℤ) : ℚ) - 1 < -ΔY.coeff F ∧ -ΔY.coeff F ≤ ((0 : ℤ) : ℚ)
    have := hΔ P
    constructor <;> push_cast <;> linarith [hlt F]

end MMP.Positivity

namespace MMP.Mori

section TieBreaker

open MMP.Threefold.Mori.Helpers

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A field essentially of finite type and formally smooth over `k` has `dim Ω_{K/k} = trdeg`. -/
private theorem finrank_kaehlerDifferential_of_formallySmooth (k K : Type*) [Field k] [Field K]
    [Algebra k K] [Algebra.EssFiniteType k K] [Algebra.FormallySmooth k K] :
    Module.finrank K Ω[K⁄k] = (Algebra.trdeg k K).toNat := by
  have h2 := (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k K).2.2
  rw [Module.finrank_zero_of_subsingleton (M := Algebra.H1Cotangent k K), Nat.cast_zero,
    sub_zero] at h2
  exact_mod_cast h2.symm

/-- On a scheme smooth over `k`, the local ring at a prime divisor `Γ` has a generator of its
top forms in degree `trdeg_k k(X)`, with nonzero image in the top forms of `k(X)`, and `k(X)` is
formally smooth over `k`. -/
private theorem exists_topForms_generator_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} [Smooth sX]
    (Γ : MMP.Mori.PrimeDivisor X) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) :
    letI := stalkAlgebra sX Γ.genericPoint
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
    (∃ σ : ⋀[Γ.localRing]^d Ω[Γ.localRing⁄k], Submodule.span Γ.localRing {σ} = ⊤ ∧
      topFormsMap k Γ.localRing X.functionField d σ ≠ 0) ∧
      Algebra.FormallySmooth k X.functionField := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  obtain ⟨hfs, -, hft⟩ := MMP.Flips.ResolutionInputs.stalk_facts (sX := sX) Γ.genericPoint
  have : Algebra.FormallySmooth k Γ.localRing := hfs
  have : Algebra.EssFiniteType k Γ.localRing := hft
  have := Γ.isDiscreteValuationRing_localRing
  have : Module.Free Γ.localRing Ω[Γ.localRing⁄k] := Module.free_of_flat_of_isLocalRing
  have : Algebra.FormallySmooth Γ.localRing X.functionField :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors Γ.localRing)
  have hK : Algebra.FormallySmooth k X.functionField :=
    Algebra.FormallySmooth.comp k Γ.localRing X.functionField
  have := essFiniteType_functionField (sX := sX)
  refine ⟨exists_topForms_generator_of_free ?_, hK⟩
  rw [← finrank_kaehlerDifferential_eq_of_isFractionRing (K := X.functionField)]
  exact (finrank_kaehlerDifferential_of_formallySmooth k X.functionField).trans hd

/-- Pull-back generators along a birational extension of a function field formally smooth over
`k`. -/
private theorem exists_isPullbackGenerator_of_formallySmooth {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (hK : letI := functionFieldAlgebra sX; Algebra.FormallySmooth k X.functionField) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    letI := functionFieldMapAlgebra f
    haveI := isScalarTower_functionFieldMap sX f
    ∃ ω : ⋀[X.functionField]^d Ω[X.functionField⁄k], IsPullbackGenerator Y.functionField ω := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have : Algebra.FormallyEtale X.functionField Y.functionField :=
    Algebra.FormallyEtale.of_equiv
      (AlgEquiv.ofBijective (Algebra.ofId X.functionField Y.functionField) hf)
  have := essFiniteType_functionField (sX := sX)
  exact exists_isPullbackGenerator_of_formallyEtale
    ((finrank_kaehlerDifferential_of_formallySmooth k X.functionField).trans hd)

/-- **The order of a pull-back along a divisor with smooth model.** If `(Y, f, E)` is a divisor
over a normal variety `X` of dimension `n` with `Y` smooth over `k`, and `v(E, Y) = v(P, X)` for
a prime divisor `P` of `X`, then `ord_E(f^*τ) = ord_P(τ)` for every rational `m`-canonical form
`τ`. -/
private theorem ordPullback_eq_ordForm_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n) (D : DivisorOver k sX)
    (hsm : Smooth (D.f ≫ sX)) (P : MMP.Mori.PrimeDivisor X)
    (hv : D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation) {m : ℤ}
    (τ : RationalPluriForms sX n m) : D.ordPullback τ = P.ordForm τ := by
  set D' := DivisorOver.ofPrimeDivisor k hX P
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isNormal
  have := D'.isLocallyNoetherian
  have := D'.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D'.f ≫ sX) := D'.isNormalVariety.1.toLocallyOfFiniteType
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (D.f ≫ sX)
  let := functionFieldAlgebra (D'.f ≫ sX)
  let := functionFieldMapAlgebra D.f
  let := functionFieldMapAlgebra D'.f
  have hT1 := isScalarTower_functionFieldMap sX D.f
  have hT2 := isScalarTower_functionFieldMap sX D'.f
  have hb1 := D.isBirationalMorphism.functionFieldMap_bijective
  have hb2 := D'.isBirationalMorphism.functionFieldMap_bijective
  let e : D.Y.functionField →+* D'.Y.functionField :=
    (functionFieldMap D'.f).comp (RingEquiv.ofBijective _ hb1).symm.toRingHom
  have he : ∀ g : X.functionField, e (functionFieldMap D.f g) = functionFieldMap D'.f g := by
    intro g
    simp only [e, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    congr 1
    exact (RingEquiv.ofBijective _ hb1).symm_apply_apply g
  let := e.toAlgebra
  have hT3 : IsScalarTower X.functionField D.Y.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun g => (he g).symm
  have hT4 : IsScalarTower k D.Y.functionField D'.Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change algebraMap k D'.Y.functionField c = e (algebraMap k D.Y.functionField c)
    rw [IsScalarTower.algebraMap_apply k X.functionField D.Y.functionField c,
      IsScalarTower.algebraMap_apply k X.functionField D'.Y.functionField c]
    exact (he _).symm
  have hesurj : Function.Surjective e := by
    intro z
    obtain ⟨g, rfl⟩ := hb2.2 z
    exact ⟨functionFieldMap D.f g, he g⟩
  have hval : ∀ y : D.Y.functionField,
      D'.E.divisorialValuation (e y) = D.E.divisorialValuation y := by
    intro y
    obtain ⟨g, rfl⟩ := hb1.2 y
    rw [he g]
    exact (congrArg (fun w => w g) hv).symm
  have hord : ∀ y : D.Y.functionField,
      D'.Y.ord (e y) D'.E.genericPoint = D.Y.ord y D.E.genericPoint := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp [Scheme.ord_zero]
    · have hey : e y ≠ 0 := (map_ne_zero e).mpr hy
      have h1 := hval y
      rw [D'.E.divisorialValuation_eq_exp_neg_ord hey, D.E.divisorialValuation_eq_exp_neg_ord hy,
        WithZero.exp_inj] at h1
      omega
  have h12 : ∀ a1 : D.E.localRing, ∃ a2 : D'.E.localRing,
      algebraMap D'.E.localRing D'.Y.functionField a2 =
        e (algebraMap D.E.localRing D.Y.functionField a1) := by
    intro a1
    have : D.E.divisorialValuation (algebraMap D.E.localRing D.Y.functionField a1) ≤ 1 :=
      (D.E.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [← hval] at this
    exact (D'.E.divisorialValuation_le_one_iff _).mp this
  have h21 : ∀ a2 : D'.E.localRing, ∃ a1 : D.E.localRing,
      e (algebraMap D.E.localRing D.Y.functionField a1) =
        algebraMap D'.E.localRing D'.Y.functionField a2 := by
    intro a2
    obtain ⟨y, hy⟩ := hesurj (algebraMap D'.E.localRing D'.Y.functionField a2)
    have : D.E.divisorialValuation y ≤ 1 := by
      rw [← hval, hy]
      exact (D'.E.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (D.E.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rwa [ha1]⟩
  obtain ⟨ψ, hψb, hψ⟩ :=
    MMP.Threefold.Mori.ModelIndependence.exists_ringHom_bijective_of_range e h12 h21
  have hd : (Algebra.trdeg k X.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hd1 : (Algebra.trdeg k D.Y.functionField).toNat = n := by
    rwa [← trdeg_functionField_eq_of_bijective sX D.f hb1]
  letI := stalkAlgebra (D.f ≫ sX) D.E.genericPoint
  letI := stalkAlgebra (D'.f ≫ sX) D'.E.genericPoint
  haveI := isScalarTower_stalk_functionField (D.f ≫ sX) D.E.genericPoint
  haveI := isScalarTower_stalk_functionField (D'.f ≫ sX) D'.E.genericPoint
  letI : Algebra D.E.localRing D'.E.localRing := ψ.toAlgebra
  letI : Algebra D.E.localRing D'.Y.functionField :=
    ((algebraMap D'.E.localRing D'.Y.functionField).comp ψ).toAlgebra
  have hS1 : IsScalarTower k D.E.localRing D'.E.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply IsFractionRing.injective D'.E.localRing D'.Y.functionField
    change _ = algebraMap D'.E.localRing D'.Y.functionField (ψ (algebraMap k D.E.localRing c))
    rw [hψ, ← IsScalarTower.algebraMap_apply k D.E.localRing D.Y.functionField c,
      ← IsScalarTower.algebraMap_apply k D'.E.localRing D'.Y.functionField c]
    exact IsScalarTower.algebraMap_apply k D.Y.functionField D'.Y.functionField c
  have hS2 : IsScalarTower D.E.localRing D'.E.localRing D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS3 : IsScalarTower D.E.localRing D.Y.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq hψ
  have hS4 : IsScalarTower k D.E.localRing D'.Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap D'.E.localRing D'.Y.functionField (ψ (algebraMap k D.E.localRing c))
    rw [IsScalarTower.algebraMap_apply k D'.E.localRing D'.Y.functionField c,
      IsScalarTower.algebraMap_apply k D.E.localRing D'.E.localRing c]
    rfl
  obtain ⟨⟨σ, hσ, h0σ⟩, hKY⟩ :=
    exists_topForms_generator_of_smooth (sX := D.f ≫ sX) D.E hd1
  have hKX : Algebra.FormallySmooth k X.functionField :=
    Algebra.FormallySmooth.of_equiv (functionFieldAlgEquiv sX D.f hb1).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_formallySmooth (sX := sX) D.f hb1 hd hKX
  obtain ⟨ω0', hω0'⟩ := exists_isPullbackGenerator_of_formallySmooth (sX := sX) D'.f hb2 hd hKX
  have hω0_2 : IsPullbackGenerator D'.Y.functionField ω0 :=
    IsPullbackGenerator.of_span hω0' hω0.1 hω0.ne_zero
  have hωb : IsPullbackGenerator D'.Y.functionField
      (topFormsMap k X.functionField D.Y.functionField n ω0) := by
    refine ⟨hω0.2.1, ?_, ?_⟩
    · rw [topFormsMap_comp]
      exact hω0_2.2.1
    · rw [topFormsMap_comp]
      exact hω0_2.2.2
  have hωT : IsPullbackGenerator D'.Y.functionField
      (topFormsMap k D.E.localRing D.Y.functionField n σ) :=
    IsPullbackGenerator.of_span hωb (span_singleton_topFormsMap (nonZeroDivisors _) hσ) h0σ
  have key := ordAt_pullbackForms_eq (k := k) (K := D.Y.functionField) (K' := D'.Y.functionField)
    (A := D.E.localRing) (A' := D'.E.localRing) (d := n) (m := m) hψb
    (v := fun y => D.Y.ord y D.E.genericPoint) (v' := fun y => D'.Y.ord y D'.E.genericPoint)
    (fun x y hx hy => D.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D.E.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => D'.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D'.E.ord_algebraMap_of_isUnit ha)
    hord hσ hωT (pullbackForms (K' := D.Y.functionField) m τ)
  have hD'eq : D'.ordPullback τ = D.ordPullback τ := by
    calc D'.ordPullback τ
        = ordAt D'.E.localRing (fun y => D'.Y.ord y D'.E.genericPoint)
            (pullbackForms (K' := D'.Y.functionField) m τ) := rfl
      _ = ordAt D'.E.localRing (fun y => D'.Y.ord y D'.E.genericPoint)
            (pullbackForms (K' := D'.Y.functionField) m
              (pullbackForms (K' := D.Y.functionField) m τ)) := by
          rw [pullbackForms_comp hω0 hωb τ]
      _ = D.ordPullback τ := key
  rw [← hD'eq]
  have h1 : (pullbackRationalPluriForms sX (𝟙 X) τ : RationalPluriForms sX n m) = τ :=
    pullbackForms_eq_self (k := k) (functionFieldMap (𝟙 X)) functionFieldMap_id_apply hω0'.1
      hω0'.ne_zero m τ
  change P.ordForm (sX := sX) (pullbackRationalPluriForms sX (𝟙 X) τ : RationalPluriForms sX n m) =
    _
  rw [h1]

/-- **The crepant boundary is the boundary along non-exceptional divisors.** Let `Δ_Y` be the
crepant boundary of `(X, Δ)` on a smooth model `f : Y → X`. If `F` is a prime divisor of `Y` that
is not `f`-exceptional, then `coeff_F Δ_Y = coeff_P Δ` for the prime divisor `P` of `X` with the
same valuation; in particular `coeff_F Δ_Y ≥ 0` when `Δ` is effective. -/
private theorem coeff_nonneg_of_not_isExceptional {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ}
    {K : MMP.Mori.Divisor X} {Δ : MMP.Mori.QDivisor X} (hΔ : Δ.IsEffective) {Y : Scheme.{u}}
    {f : Y ⟶ X} (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (hsm : Smooth (f ≫ sX)) {ΔY : MMP.Mori.QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) (F : MMP.Mori.PrimeDivisor Y)
    (hE : ¬ RationalMap.IsExceptional (X := Y) f.toRationalMap F) :
    0 ≤ ΔY.coeff F := by
  set D : DivisorOver k sX := ⟨Y, f, hY, hf, F⟩
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hmτ⟩ := hΔY F
  obtain ⟨P, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hE
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  rw [ordPullback_eq_ordForm_of_smooth hX hn D hsm P hv τ] at hmτ
  have hx : D.f D.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hPU : (P.support ∩ (U : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hx ▸ hU⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have e := hτ.2 P hPU
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  have h0 : (0 : ℚ) ≤ Δ.coeff P := hΔ P
  have : (m : ℚ) * ΔY.coeff F = m * Δ.coeff P := by linear_combination -hmτ - e
  have := mul_left_cancel₀ hm0.ne' this
  linarith

/-- The coefficient of `∑_{j ∈ s} c_j F_j` along `F_i`, for an injective family `F`. -/
private theorem coeff_sum_single_apply {Y : Scheme.{u}} {ι : Type*} {R : Type*}
    [AddCommMonoid R] {F : ι → MMP.Mori.PrimeDivisor Y} (hF : Function.Injective F)
    [DecidableEq ι] (s : Finset ι) (c : ι → R) (i : ι) :
    MMP.Mori.DivisorWithCoeffs.coeff (∑ j ∈ s, Finsupp.single (F j) (c j)) (F i) =
      if i ∈ s then c i else 0 := by
  change (∑ j ∈ s, Finsupp.single (F j) (c j)) (F i) = _
  rw [Finsupp.finset_sum_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single i (fun j _ hji => Finsupp.single_eq_of_ne (hF.ne hji.symm))
      (fun h => absurd hi h), Finsupp.single_eq_same]
  · exact Finset.sum_eq_zero fun j hj =>
      Finsupp.single_eq_of_ne (hF.ne fun h : j = i => hi (h ▸ hj)).symm

/-- A coefficient of the test boundary `∑_{j ≠ j'} α_j F_j` is either `0` or `α_i` along some
`F_i` with `i ≠ j'`. -/
private theorem coeff_tieBreakerBoundary_eq_zero_or {Y : Scheme.{u}} {s : ℕ}
    {F : Fin s → MMP.Mori.PrimeDivisor Y} (hF : Function.Injective F) (r a p : Fin s → ℚ)
    (j' : Fin s) (c : ℚ) (E : MMP.Mori.PrimeDivisor Y) :
    (tieBreakerBoundary F r a p j' c).coeff E = 0 ∨ ∃ i, i ≠ j' ∧ F i = E ∧
      (tieBreakerBoundary F r a p j' c).coeff E = -c * r i + a i - p i := by
  by_cases hEF : ∃ i, F i = E
  · obtain ⟨i, rfl⟩ := hEF
    rw [tieBreakerBoundary, coeff_sum_single_apply hF]
    split_ifs with hi
    · exact .inr ⟨i, Finset.ne_of_mem_erase hi, rfl, rfl⟩
    · exact .inl rfl
  · push Not at hEF
    refine .inl ?_
    change (∑ j ∈ _, Finsupp.single (F j) _) E = 0
    rw [Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun j _ => Finsupp.single_eq_of_ne (hEF j).symm

/-- In an adapted resolution, the discrepancy `a_i` along a non-exceptional `F_i` is `≤ 0`: the
crepant boundary `-∑_j a_j F_j` restricts to the effective `Δ` there. -/
private theorem aj_nonpos_of_not_isExceptional {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : MMP.Mori.Divisor X}
    {Δ : MMP.Mori.QDivisor X} {D : MMP.Mori.Divisor X} {a : ℚ} {m : ℕ} {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {s : ℕ}
    {F : Fin s → MMP.Mori.PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsBasepointFreeAdaptedResolution sX n K Δ D a m f F aj pj rj) (i : Fin s)
    (hex : ¬ RationalMap.IsExceptional (X := Y) f.toRationalMap (F i)) : aj i ≤ 0 := by
  obtain ⟨hY, hcb⟩ := h.isCrepantBoundary
  have h0 := coeff_nonneg_of_not_isExceptional h.isEffective hY
    h.isLogResolution.isBirationalMorphism h.isLogResolution.isSmoothScheme.smooth hcb (F i) hex
  rw [DivisorWithCoeffs.coeff_neg, coeff_sum_single_apply h.injective,
    if_pos (Finset.mem_univ i)] at h0
  linarith

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]

/-- **The round-up of the test boundary is effective and exceptional.** For a tie-breaker
`(j', c)` of an `m`-adapted resolution `(f; F_•; a_•; p_•; r_•)` of a basepoint-free datum, the
round-up of the test boundary `A = ∑_{j ≠ j'} (-c r_j + a_j - p_j) F_j` is effective, and every
prime divisor of `Y` with nonzero coefficient in `⌈A⌉` is `f`-exceptional. -/
@[mmp "lem_km3a_bpf_test_boundary_roundup"]
public theorem IsBasepointFreeTieBreaker.isEffective_roundUp_tieBreakerBoundary {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ} {m : ℕ} {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} {s : ℕ}
    {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ} {j' : Fin s} {c : ℚ}
    (h : IsBasepointFreeTieBreaker sX n K Δ D a m f F aj pj rj j' c) :
    (tieBreakerBoundary F (fun j => (rj j : ℚ)) aj pj j' c).roundUp.IsEffective ∧
      ∀ E : PrimeDivisor Y,
        (tieBreakerBoundary F (fun j => (rj j : ℚ)) aj pj j' c).roundUp.coeff E ≠ 0 →
          RationalMap.IsExceptional (X := Y) f.toRationalMap E := by
  have hceil : ∀ i, i ≠ j' → (-1 : ℤ) < ⌈-c * (rj i : ℚ) + aj i - pj i⌉ := fun i hi =>
    Int.lt_ceil.mpr (by exact_mod_cast h.neg_one_lt i hi)
  refine ⟨fun E => ?_, fun E hE => ?_⟩ <;>
    rcases coeff_tieBreakerBoundary_eq_zero_or h.injective (fun j => (rj j : ℚ)) aj pj j' c E
      with h0 | ⟨i, hi, rfl, hα⟩
  · change (0 : ℤ) ≤ DivisorWithCoeffs.coeff _ E
    simp [DivisorWithCoeffs.coeff_roundUp, h0]
  · change (0 : ℤ) ≤ DivisorWithCoeffs.coeff _ (F i)
    rw [DivisorWithCoeffs.coeff_roundUp, hα]
    linarith [hceil i hi]
  · simp [DivisorWithCoeffs.coeff_roundUp, h0] at hE
  · rw [DivisorWithCoeffs.coeff_roundUp, hα] at hE
    by_contra hex
    have hpos : 0 < -c * (rj i : ℚ) + aj i - pj i :=
      Int.ceil_pos.mp (by have := hceil i hi; omega)
    nlinarith [h.pos_c, h.pos_p i, (Nat.cast_nonneg (rj i) : (0 : ℚ) ≤ rj i),
      aj_nonpos_of_not_isExceptional h.toIsBasepointFreeAdaptedResolution i hex]

end TieBreaker

end MMP.Mori

namespace MMP.Threefold.Bridges

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral
attribute [local instance] globalSectionsModule

section Vanishing

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- The coefficient vectors `c` whose section `∑ᵢ cᵢ sᵢ` vanishes at the point `z`, a
`k`-subspace of `kᴺ⁺¹`. -/
private noncomputable def vanishingSubspace (s : Fin (N + 1) → Γ(L, ⊤)) (z : X) :
    Submodule k (Fin (N + 1) → k) where
  carrier := {c | z ∉ nonvanishingOpen X L (systemSection s c)}
  zero_mem' := by
    simp [Stacks.NonvanishingOpen.mem_nonvanishingOpen]
  add_mem' {a b} ha hb := by
    intro h
    rw [Set.mem_setOf_eq, map_add] at *
    rcases Stacks.Ample.nonvanishingLocus_add_subset L _ _ h with h' | h'
    · exact ha h'
    · exact hb h'
  smul_mem' a c hc := by
    intro h
    rw [Set.mem_setOf_eq, map_smul] at *
    exact hc (Stacks.Ample.nonvanishingLocus_smul_subset L
      (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k X a) _ h)

end Vanishing

/-- The linear polynomial `∑ᵢ ℓ(eᵢ) Tᵢ` of a linear form `ℓ` on `kᴺ⁺¹`. -/
private noncomputable def linearPoly {k : Type u} [Field k] {N : ℕ}
    (ℓ : (Fin (N + 1) → k) →ₗ[k] k) : MvPolynomial (Fin (N + 1)) k :=
  ∑ i, MvPolynomial.C (ℓ (Pi.single i 1)) * MvPolynomial.X i

private theorem eval_linearPoly {k : Type u} [Field k] {N : ℕ}
    (ℓ : (Fin (N + 1) → k) →ₗ[k] k) (c : Fin (N + 1) → k) :
    MvPolynomial.eval c (linearPoly ℓ) = ℓ c := by
  classical
  rw [linearPoly, map_sum, LinearMap.pi_apply_eq_sum_univ ℓ c]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, smul_eq_mul]
  rw [mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

private theorem isHomogeneous_linearPoly {k : Type u} [Field k] {N : ℕ}
    (ℓ : (Fin (N + 1) → k) →ₗ[k] k) : (linearPoly ℓ).IsHomogeneous 1 :=
  MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ =>
    (MvPolynomial.isHomogeneous_C_mul_X _ i)

/-- Finitely many proper subspaces of `kᴺ⁺¹` are avoided off the zero locus of a single nonzero
homogeneous polynomial. -/
private theorem exists_isHomogeneous_notMem {k : Type u} [Field k] {N : ℕ} {ι : Type*}
    [Fintype ι] (W : ι → Submodule k (Fin (N + 1) → k)) (hW : ∀ j, W j ≠ ⊤) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ Q.IsHomogeneous (Fintype.card ι) ∧
      ∀ c, MvPolynomial.eval c Q ≠ 0 → ∀ j, c ∉ W j := by
  choose c₀ hc₀ using fun j => SetLike.exists_not_mem_of_ne_top (W j) (hW j) rfl
  choose ℓ hℓ hker using fun j => Submodule.exists_le_ker_of_notMem (hc₀ j)
  refine ⟨∏ j, linearPoly (ℓ j), Finset.prod_ne_zero_iff.mpr fun j _ h0 => hℓ j ?_, ?_,
    fun c hc j hcj => hc ?_⟩
  · rw [← eval_linearPoly, h0, map_zero]
  · convert
      MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => isHomogeneous_linearPoly (ℓ j)
    simp
  · rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [eval_linearPoly]; exact hker j hcj)

/-- **General members of a free linear system avoid given subvarieties.** Let `X` be a variety
over a field `k`, `L` an invertible sheaf on `X`, and `s₀, …, s_N` sections spanning a linear
system `V ⊆ H⁰(X, L)` that generates `L`. For finitely many irreducible closed subsets `Z_j ⊆ X`
there are a dense open of the coefficient space `kᴺ⁺¹` and a dense open of `ℙ(V) = ℙᴺ_k` such that
for every coefficient vector `c` in the first, and every `c ≠ 0` with `[c]` in the second, the
member `Z(∑ᵢ cᵢ sᵢ)` contains no `Z_j`, i.e. each `Z_j` meets the non-vanishing locus of
`∑ᵢ cᵢ sᵢ`. -/
@[mmp "lem_km5d_general_member_avoids"]
public theorem exists_dense_open_inter_nonvanishingOpen_nonempty {k : Type u} [Field k] {N : ℕ}
    {X : Scheme.{u}} [X.Over (Spec (.of k))] (hX : MMP.Mori.IsVariety k (X ↘ Spec (.of k)))
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    {ι : Type*} [Finite ι] (Z : ι → Set X) (hZc : ∀ j, IsClosed (Z j))
    (hZi : ∀ j, IsIrreducible (Z j)) :
    (∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U →
        ∀ j, (Z j ∩ nonvanishingOpen X L (systemSection s c)).Nonempty) ∧
    (∃ U : (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        ∀ j, (Z j ∩ nonvanishingOpen X L (systemSection s c)).Nonempty) := by
  classical
  haveI := Fintype.ofFinite ι
  choose z hz using fun j => (hZi j).nonempty
  -- some member of the system does not vanish at `z j`
  have hW : ∀ j, vanishingSubspace s (z j) ≠ ⊤ := fun j htop => by
    obtain ⟨c, hc⟩ := Opens.mem_iSup.mp (hs.symm ▸ trivial : z j ∈ ⨆ c : Fin (N + 1) → k,
      nonvanishingOpen X L (systemSection s c))
    exact (htop ▸ Submodule.mem_top : c ∈ vanishingSubspace s (z j)) hc
  obtain ⟨Q, hQ0, hQhom, hQ⟩ := exists_isHomogeneous_notMem _ hW
  have key : ∀ c : Fin (N + 1) → k, MvPolynomial.eval c Q ≠ 0 →
      ∀ j, (Z j ∩ nonvanishingOpen X L (systemSection s c)).Nonempty := fun c hc j =>
    ⟨z j, hz j, by_contra fun h => hQ c hc j h⟩
  refine ⟨⟨PrimeSpectrum.basicOpen Q, dense_basicOpen_of_ne_zero hQ0,
      fun c hc => key c fun h0 => hc (RingHom.mem_ker.mpr h0)⟩,
    ⟨ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) Q,
      dense_projectiveSpace_basicOpen hQ0, fun c hc hmem => key c fun h0 =>
        hmem (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨_, hQhom⟩
          (RingHom.mem_ker.mpr h0))⟩⟩

end MMP.Threefold.Bridges
