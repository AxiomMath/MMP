module

public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.DeRham.Logarithmic.RelativeLogForms

/-!
# The fractional logarithmic complex of a root of `𝒪_V(NB)`: existence and residues

Let `V` be smooth projective over `ℂ`, `D = S + Supp B` a simple normal crossing divisor with `S`
reduced and `B = Bn/N` with coefficients in `(0, 1)`, and `𝒪_V(M)` an `N`-th root of `𝒪_V(Bn)`
through `NM = Bn + div ψ`. On `U' = V ∖ (D ∪ Supp M)` the function `ψ` is a unit `u`, and the
connection `∇ = d - N⁻¹ (du/u) ∧` preserves the subsheaf
`C^p = 𝒪_V(-M) · Ω^p_V(log D)(-S)` of the forms on `U'`; with it `C^•` is a complex whose
connection has residue `Bn(E)/N` along each component `E` of `Supp B`. This file builds `C^•`
and its connection and computes the residues; the degeneration of its Hodge-to-de Rham spectral
sequence at `E₁` is proved separately.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.Cond`: the sections of `C^p` among the forms on `U'`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.twT`, `MMP.FourfoldProofs.FractionalLogComplexProof.nab`:
  the twisted differential `d - θ ∧` on the total ring of forms.
* `MMP.FourfoldProofs.FractionalLogComplexProof.GenData`: local generators `g₀` of `𝒪_V(-M)` with
  `∇ g₀ = g₀ ξ₀` for a logarithmic `1`-form `ξ₀`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_genData`: generator data exist near every
  point.
* `MMP.FourfoldProofs.FractionalLogComplexProof.nabStable_of_genData`: `∇` preserves `C^•`.

## Implementation notes

Forms of all degrees are compared in the total ring of `Ω^•_{U/ℂ}`, `U = V ∖ D`, which is graded
commutative; functions act through its central structure map. Locally every section of `C^p` is
a sum of products `b · dc₁ ∧ ⋯ ∧ dc_p` of functions and exact forms, on which the de Rham
differential is `db ∧ dc₁ ∧ ⋯ ∧ dc_p`; all identities involving `d` are verified on such
products and glued.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite MMP MMP.Mori
    MMP.Mori.Divisor

attribute [local instance] HasDerivedCategory.standard

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

/-! ### Products of anticommuting square-zero elements -/

section AntiComm

variable {T : Type*} [Ring T] {ι : Type*} (θ : ι → T)

/-- Permuting the factors of a product of pairwise anticommuting elements changes it at most
by a sign. -/
theorem prod_map_perm (hac : ∀ i j, θ i * θ j = -(θ j * θ i)) {l₁ l₂ : List ι}
    (h : l₁.Perm l₂) :
    (l₁.map θ).prod = (l₂.map θ).prod ∨ (l₁.map θ).prod = -(l₂.map θ).prod := by
  induction h with
  | nil => exact Or.inl rfl
  | cons x _ ih =>
    rcases ih with ih | ih
    · exact Or.inl (by simp [ih])
    · exact Or.inr (by simp [ih])
  | swap x y l =>
    right
    simp only [List.map_cons, List.prod_cons, ← mul_assoc, hac y x, neg_mul]
  | trans _ _ ih₁ ih₂ =>
    rcases ih₁ with h₁ | h₁ <;> rcases ih₂ with h₂ | h₂
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inr (h₁.trans h₂)
    · exact Or.inr (by rw [h₁, h₂])
    · exact Or.inl (by rw [h₁, h₂, neg_neg])

/-- A product of pairwise anticommuting square-zero elements with a repeated factor vanishes. -/
theorem prod_map_eq_zero_of_not_nodup (hsq : ∀ i, θ i * θ i = 0)
    (hac : ∀ i j, θ i * θ j = -(θ j * θ i)) {l : List ι} (h : ¬ l.Nodup) :
    (l.map θ).prod = 0 := by
  classical
  rw [List.nodup_iff_count_le_one] at h
  simp only [not_forall, not_le] at h
  obtain ⟨a, ha⟩ := h
  have ha1 : a ∈ l := List.count_pos_iff.mp (by omega)
  have ha2 : a ∈ l.erase a := by
    rw [← List.count_pos_iff, List.count_erase_self]
    omega
  have hp : l.Perm (a :: a :: (l.erase a).erase a) :=
    (List.perm_cons_erase ha1).trans (List.Perm.cons a (List.perm_cons_erase ha2))
  rcases prod_map_perm θ hac hp with e | e <;>
    simp [e, ← mul_assoc, hsq a]

/-- The product of the elements indexed by two finite sets, each in increasing order, is up to
sign the product indexed by their union when they are disjoint, and vanishes otherwise. -/
theorem prod_sort_mul_prod_sort [LinearOrder ι] (hsq : ∀ i, θ i * θ i = 0)
    (hac : ∀ i j, θ i * θ j = -(θ j * θ i)) (K L : Finset ι) :
    ((K.sort (· ≤ ·)).map θ).prod * ((L.sort (· ≤ ·)).map θ).prod = 0 ∨
      ((K.sort (· ≤ ·)).map θ).prod * ((L.sort (· ≤ ·)).map θ).prod =
        (((K ∪ L).sort (· ≤ ·)).map θ).prod ∨
      ((K.sort (· ≤ ·)).map θ).prod * ((L.sort (· ≤ ·)).map θ).prod =
        -(((K ∪ L).sort (· ≤ ·)).map θ).prod := by
  rw [← List.prod_append, ← List.map_append]
  by_cases hnd : (K.sort (· ≤ ·) ++ L.sort (· ≤ ·)).Nodup
  · right
    refine prod_map_perm θ hac (List.perm_of_nodup_nodup_toFinset_eq hnd
      (Finset.sort_nodup _ _) ?_)
    ext x
    simp
  · exact Or.inl (prod_map_eq_zero_of_not_nodup θ hsq hac hnd)

end AntiComm

/-! ### Coordinates of a smooth algebra are non-zero-divisors -/

section Coordinates

/-- **Coordinates are non-zero-divisors.** If `B` is smooth over `R` and the differentials of
`t₁, …, tₙ` form a basis of `Ω[B⁄R]`, then each `tᵢ` is a non-zero-divisor of `B`. -/
theorem isSMulRegular_of_basis_D {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.Smooth R B] {n : ℕ} (t : Fin n → B) (b : Module.Basis (Fin n) B Ω[B⁄R])
    (hb : ∀ i, b i = KaehlerDifferential.D R B (t i)) (i : Fin n) : IsSMulRegular B (t i) := by
  let P := MvPolynomial (Fin n) R
  let _ : Algebra P B := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have : IsScalarTower R P B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, P]
  have hX : ∀ i, algebraMap P B (MvPolynomial.X i) = t i := fun i => by
    simp [RingHom.algebraMap_toAlgebra, P]
  let bP := (KaehlerDifferential.mvPolynomialBasis R (Fin n)).baseChange B
  have hmap :
      KaehlerDifferential.mapBaseChange R P B = (bP.equiv b (Equiv.refl _)).toLinearMap := by
    refine bP.ext fun i => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, hb]
    simp only [bP, Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply]
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, hX]
  have hbij : Function.Bijective (KaehlerDifferential.mapBaseChange R P B) := by
    rw [hmap]
    exact (bP.equiv b (Equiv.refl _)).bijective
  have : Subsingleton Ω[B⁄P] := subsingleton_of_forall_eq 0 fun z => by
    obtain ⟨w, rfl⟩ := KaehlerDifferential.map_surjective R P B z
    exact (KaehlerDifferential.exact_mapBaseChange_map R P B w).mpr (hbij.2 w)
  have : Subsingleton (Algebra.H1Cotangent P B) := subsingleton_of_forall_eq 0 fun z => by
    have hδ : Algebra.H1Cotangent.δ R P B z = 0 :=
      hbij.1 ((Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨z, rfl⟩ |>.trans
        (map_zero _).symm)
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B z).mp hδ
    rw [Subsingleton.elim w 0, map_zero]
  have : Algebra.FormallyEtale P B :=
    (Algebra.formallyEtale_iff P B).mpr ⟨inferInstance, inferInstance⟩
  have : Algebra.FinitePresentation P B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R P B
  have : Algebra.Etale P B := ⟨inferInstance, inferInstance⟩
  rw [← hX]
  exact IsSMulRegular.of_flat (MvPolynomial.isRegular_X.left)

/-- A basis of exact differentials transfers along a formally étale ring map. -/
theorem exists_basis_D_of_comp {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    (α : R →+* A) (β : A →+* C) (γ : R →+* C) (hγ : γ = β.comp α)
    (hβ : letI := β.toAlgebra; Algebra.FormallyEtale A C) {n : ℕ} (t : Fin n → A)
    (hb : letI := α.toAlgebra
      ∃ b : Module.Basis (Fin n) A Ω[A⁄R], ∀ i, b i = KaehlerDifferential.D R A (t i)) :
    letI := γ.toAlgebra
    ∃ b : Module.Basis (Fin n) C Ω[C⁄R], ∀ i, b i = KaehlerDifferential.D R C (β (t i)) := by
  let _ := α.toAlgebra
  let _ := β.toAlgebra
  let _ := γ.toAlgebra
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, hγ]
  obtain ⟨b, hb⟩ := hb
  refine ⟨(KaehlerDifferential.isBaseChange_of_formallyEtale R A C).basis b, fun i => ?_⟩
  rw [IsBaseChange.basis_apply, hb, KaehlerDifferential.map_D]
  rfl

end Coordinates

section CoordIdeals

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- Two distinct coordinates vanishing at a prime cannot divide each other near that prime. -/
theorem not_mul_eq_mul_of_basis_D {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (𝔭 : Ideal B) {i k : Fin n} (hik : i ≠ k) (hi : t i ∈ 𝔭) (hk : t k ∈ 𝔭)
    {s c : B} (hs : s ∉ 𝔭) (h : s * t i = c * t k) : False := by
  have hD := congrArg (fun x => b.coord i (KaehlerDifferential.D R B x)) h
  simp only [Derivation.leibniz, map_add, map_smul, ← hb, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hD
  rw [Finsupp.single_apply, ite_eq_right hik.symm, mul_zero, zero_add] at hD
  apply hs
  have : s = t k * (b.repr (KaehlerDifferential.D R B c)) i -
      t i * (b.repr (KaehlerDifferential.D R B s)) i := by
    linear_combination hD
  rw [this]
  exact 𝔭.sub_mem (𝔭.mul_mem_right _ hk) (𝔭.mul_mem_right _ hi)

omit [Algebra R B] in
/-- An element outside every minimal prime of a radical ideal `J` is a non-zero-divisor
modulo `J`. -/
theorem mem_of_mul_mem_of_forall_minimalPrimes {J : Ideal B}
    (hJ : J.IsRadical) {a x : B} (hx : ∀ 𝔮 ∈ J.minimalPrimes, x ∉ 𝔮) (h : a * x ∈ J) :
    a ∈ J := by
  rw [← hJ.radical, ← Ideal.sInf_minimalPrimes] at h ⊢
  rw [Ideal.mem_sInf] at h ⊢
  intro 𝔮 h𝔮
  exact (h𝔮.1.1.mem_or_mem (h h𝔮)).resolve_right (hx 𝔮 h𝔮)

omit [Algebra R B] in
/-- At a minimal prime `𝔮` of a radical ideal `J` of a Noetherian ring, every element of `𝔮`
times some element outside `𝔮` lies in `J`. -/
theorem exists_mul_mem_of_mem_minimalPrimes_of_isRadical [IsNoetherianRing B] {J : Ideal B}
    (hJ : J.IsRadical) {𝔮 : Ideal B} (h𝔮 : 𝔮 ∈ J.minimalPrimes) {x : B} (hx : x ∈ 𝔮) :
    ∃ y ∉ 𝔮, x * y ∈ J := by
  classical
  have hfin : J.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing B J
  have hp : 𝔮.IsPrime := h𝔮.1.1
  have hsep : ∀ 𝔮' ∈ J.minimalPrimes, 𝔮' ≠ 𝔮 → ∃ y ∈ 𝔮', y ∉ 𝔮 := by
    intro 𝔮' h𝔮' hne
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hne (le_antisymm hcon (h𝔮.2 ⟨h𝔮'.1.1, h𝔮'.1.2⟩ hcon))
  choose! yf hyf₁ hyf₂ using hsep
  let F := hfin.toFinset.erase 𝔮
  refine ⟨∏ 𝔮' ∈ F, yf 𝔮', ?_, ?_⟩
  · intro hmem
    obtain ⟨𝔮', h𝔮'F, hmem'⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    obtain ⟨hne, h𝔮'm⟩ := Finset.mem_erase.mp h𝔮'F
    exact hyf₂ 𝔮' ((Set.Finite.mem_toFinset _).mp h𝔮'm) hne hmem'
  · rw [← hJ.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro 𝔮'' h𝔮''
    by_cases he : 𝔮'' = 𝔮
    · exact he ▸ Ideal.mul_mem_right _ _ hx
    · refine Ideal.mul_mem_left _ _ ?_
      have hmem : 𝔮'' ∈ F := Finset.mem_erase.mpr ⟨he, (Set.Finite.mem_toFinset _).mpr h𝔮''⟩
      rw [← Finset.mul_prod_erase F _ hmem]
      exact Ideal.mul_mem_right _ _ (hyf₁ 𝔮'' h𝔮'' he)

/-- A coordinate lies in no minimal prime of the (radical) ideal of another coordinate. -/
theorem notMem_of_mem_minimalPrimes_span_coord [IsNoetherianRing B] {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    {i k : Fin n} (hik : i ≠ k) (hrad : (Ideal.span {t k}).IsRadical)
    {𝔮 : Ideal B} (h𝔮 : 𝔮 ∈ (Ideal.span {t k}).minimalPrimes) : t i ∉ 𝔮 := by
  intro hi
  have hk : t k ∈ 𝔮 := h𝔮.1.2 (Ideal.subset_span rfl)
  obtain ⟨y, hy, hmem⟩ := exists_mul_mem_of_mem_minimalPrimes_of_isRadical hrad h𝔮 hi
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  exact not_mul_eq_mul_of_basis_D t b hb 𝔮 hik hi hk hy (by rw [mul_comm, ← hc])

/-- **The ideal of a product of distinct coordinates is the intersection of their ideals**, when
each coordinate ideal is radical; see `isRadical_span_prod_of_basis_D` for radicality. -/
theorem span_prod_eq_iInf_of_basis_D [IsNoetherianRing B] {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (S : Finset (Fin n)) (hrad : ∀ k ∈ S, (Ideal.span {t k}).IsRadical) :
    Ideal.span {∏ i ∈ S, t i} = ⨅ i ∈ S, Ideal.span {t i} := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hkS ih =>
    rw [Finset.prod_insert hkS, Finset.iInf_insert, ← ih (fun j hj => hrad j
        (Finset.mem_insert_of_mem hj))]
    apply le_antisymm
    · refine le_inf ?_ ?_
      · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)
      · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)
    · intro x ⟨hxk, hxS⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hxS
      have ha : a ∈ Ideal.span {t k} := by
        refine mem_of_mul_mem_of_forall_minimalPrimes (hrad k (Finset.mem_insert_self _ _))
          (fun 𝔮 h𝔮 hmem => ?_) hxk
        have hp : 𝔮.IsPrime := h𝔮.1.1
        obtain ⟨i, hiS, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
        exact notMem_of_mem_minimalPrimes_span_coord t b hb
          (fun h : i = k => hkS (h ▸ hiS)) (hrad k (Finset.mem_insert_self _ _)) h𝔮 hi
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩

/-- If the differentials of `t₁, …, tₙ` form a basis of `Ω[B⁄R]` and each ideal `(t_k)`, `k ∈ S`,
is radical, then the ideal generated by `∏_{k ∈ S} t_k` is radical. -/
theorem isRadical_span_prod_of_basis_D [IsNoetherianRing B] {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (S : Finset (Fin n)) (hrad : ∀ k ∈ S, (Ideal.span {t k}).IsRadical) :
    (Ideal.span {∏ i ∈ S, t i}).IsRadical := by
  rw [span_prod_eq_iInf_of_basis_D t b hb S hrad]
  exact Ideal.isRadical_iInf _ fun i => Ideal.isRadical_iInf _ fun hi => hrad i hi

end CoordIdeals

/-! ### The total ring of relative differential forms -/

section Forms

variable {Y S : Scheme.{u}} (g : Y ⟶ S)

/-- The graded algebra of relative differential forms of `g`, as a presheaf graded algebra. -/
noncomputable abbrev TB :=
  (Scheme.Hom.relativeDifferentialFormsAlgebra g).toPresheafGradedAlgebra

/-- The structure map `𝒪_Y(O) → Ω^•_{Y/S}(O)`. -/
noncomputable def sm (O : Y.Opens) : Γ(Y, O) →+* (TB g).Total (op O) :=
  (TB g).structureMap (op O)

/-- A section of `Ω_{Y/S}`, read as a degree-one element of the total ring of forms. -/
noncomputable def ι1 (O : Y.Opens)
    (ξ : (Scheme.Hom.relativeDifferentials g).val.obj (op O)) : (TB g).Total (op O) :=
  (TB g).incl 1
    ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials g)).val.app (op O) ξ)

/-- The exact one-form `d a`, as a degree-one element of the total ring of forms. -/
noncomputable def δ (O : Y.Opens) (a : Γ(Y, O)) : (TB g).Total (op O) :=
  ι1 g O ((Scheme.Hom.universalRelativeDerivation g).d (X := op O) a)

variable {g}

/-- Functions are central in the total ring of forms. -/
theorem sm_comm {O : Y.Opens} (c : Γ(Y, O)) (z : (TB g).Total (op O)) :
    sm g O c * z = z * sm g O c :=
  (TB g).structureMap_commutes _ c z

/-- A function acts on the total ring of forms by multiplication by its image under `sm`. -/
theorem smul_eq_sm_mul {O : Y.Opens}
    (c : (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O))
    (z : (TB g).Total (op O)) :
    c • z = sm g O c * z := by
  change _ = c • (1 : (TB g).Total (op O)) * z
  rw [(TB g).smul_mul_eq, one_mul]

/-- The product of the image of a function `c` with a `p`-form `x` is the `p`-form `c • x`. -/
theorem sm_mul_incl {O : Y.Opens}
    (c : (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O)) (p : ℤ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.obj (op O)) :
    sm g O c * (TB g).incl p x = (TB g).incl p (c • x) :=
  ((smul_eq_sm_mul c _).symm.trans ((TB g).incl_smul p c x).symm)

/-- `ι1` is additive. -/
theorem ι1_add {O : Y.Opens} (ξ η : (Scheme.Hom.relativeDifferentials g).val.obj (op O)) :
    ι1 g O (ξ + η) = ι1 g O ξ + ι1 g O η :=
  (congrArg ((TB g).incl 1) (map_add _ ξ η)).trans ((TB g).incl_add 1 _ _)

/-- `ι1 (c • ξ) = c · ι1 ξ` for a function `c`. -/
theorem ι1_smul {O : Y.Opens} (c : Y.ringCatSheaf.obj.obj (op O))
    (ξ : (Scheme.Hom.relativeDifferentials g).val.obj (op O)) :
    ι1 g O (c • ξ) = sm g O c * ι1 g O ξ :=
  (congrArg ((TB g).incl 1)
    (((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials g)).val.app
      (op O)).hom.map_smul c ξ)).trans
    (sm_mul_incl (g := g)
      (show (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O) from c) 1
      _).symm

/-- A one-form squares to zero in the total ring of forms. -/
theorem ι1_mul_self {O : Y.Opens}
    (ξ : (Scheme.Hom.relativeDifferentials g).val.obj (op O)) :
    ι1 g O ξ * ι1 g O ξ = 0 := by
  have h := (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
    (Scheme.Hom.relativeDifferentials g)).1 (op O) ξ
  refine ((TB g).incl_mul_incl 1 1 _ _).trans ?_
  refine (congrArg ((TB g).incl (1 + 1)) h).trans ?_
  exact (TB g).incl_zero _

/-- One-forms anticommute in the total ring of forms. -/
theorem ι1_anticomm {O : Y.Opens}
    (ξ η : (Scheme.Hom.relativeDifferentials g).val.obj (op O)) :
    ι1 g O ξ * ι1 g O η = -(ι1 g O η * ι1 g O ξ) := by
  have h := ι1_mul_self (g := g) (ξ + η)
  rw [ι1_add, add_mul, mul_add, mul_add, ι1_mul_self, ι1_mul_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The Leibniz rule `d(ab) = a db + b da`. -/
theorem δ_mul {O : Y.Opens} (a b : Γ(Y, O)) :
    δ g O (a * b) = sm g O a * δ g O b + sm g O b * δ g O a := by
  refine (congrArg (ι1 g O)
    ((Scheme.Hom.universalRelativeDerivation g).d_mul (X := op O) a b)).trans ?_
  refine (ι1_add _ _).trans ?_
  exact congrArg₂ (· + ·) (ι1_smul _ _) (ι1_smul _ _)

/-- `d 1 = 0`. -/
theorem δ_one {O : Y.Opens} : δ g O 1 = 0 := by
  refine (congrArg (ι1 g O) ((Scheme.Hom.universalRelativeDerivation g).d_one (op O))).trans ?_
  refine (congrArg ((TB g).incl 1) (map_zero _)).trans ?_
  exact (TB g).incl_zero _

/-- `d(a + b) = da + db`. -/
theorem δ_add {O : Y.Opens} (a b : Γ(Y, O)) :
    δ g O (a + b) = δ g O a + δ g O b :=
  (congrArg (ι1 g O) (map_add _ a b)).trans (ι1_add _ _)

/-- Exact one-forms anticommute: `da ∧ db = -(db ∧ da)`. -/
theorem δ_anticomm {O : Y.Opens} (a b : Γ(Y, O)) :
    δ g O a * δ g O b = -(δ g O b * δ g O a) :=
  ι1_anticomm _ _

/-- `da ∧ da = 0`. -/
theorem δ_mul_self {O : Y.Opens} (a : Γ(Y, O)) : δ g O a * δ g O a = 0 :=
  ι1_mul_self _

/-- `ι1` commutes with restriction. -/
theorem totalRestrict_ι1 {O O' : Y.Opens} (φ : op O ⟶ op O')
    (ξ : (Scheme.Hom.relativeDifferentials g).val.obj (op O)) :
    (TB g).totalRestrict φ (ι1 g O ξ) =
      ι1 g O' ((Scheme.Hom.relativeDifferentials g).val.map φ ξ) :=
  ((TB g).totalRestrict_incl _ 1 _).trans (congrArg ((TB g).incl 1)
    (PresheafOfModules.naturality_apply
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials g)).val φ ξ).symm)

/-- The exact one-form `da` commutes with restriction. -/
theorem totalRestrict_δ {O O' : Y.Opens} (φ : op O ⟶ op O') (a : Γ(Y, O)) :
    (TB g).totalRestrict φ (δ g O a) = δ g O' (Y.presheaf.map φ a) :=
  (totalRestrict_ι1 φ _).trans (congrArg (ι1 g O')
    ((Scheme.Hom.universalRelativeDerivation g).d_map φ a).symm)

/-- The structure map `sm` commutes with restriction. -/
theorem totalRestrict_sm {O O' : Y.Opens} (φ : op O ⟶ op O') (c : Γ(Y, O)) :
    (TB g).totalRestrict φ (sm g O c) = sm g O' (Y.presheaf.map φ c) :=
  (TB g).structureMap_naturality _ c

/-- A function times a wedge of exact one-forms, `b · d c₁ ∧ ⋯ ∧ d cₚ`. -/
noncomputable def mon (g : Y ⟶ S) (O : Y.Opens) (b : Γ(Y, O)) (l : List Γ(Y, O)) :
    (TB g).Total (op O) :=
  sm g O b * (l.map (δ g O)).prod

/-- The differential of `b · d c₁ ∧ ⋯ ∧ d cₚ`, namely `d b ∧ d c₁ ∧ ⋯ ∧ d cₚ`. -/
noncomputable def dmon (g : Y ⟶ S) (O : Y.Opens) (b : Γ(Y, O)) (l : List Γ(Y, O)) :
    (TB g).Total (op O) :=
  δ g O b * (l.map (δ g O)).prod

/-- **The de Rham rule in the total ring.** `b · d c₁ ∧ ⋯ ∧ d cₚ` is homogeneous of degree `p`, and
the de Rham differential carries it to `d b ∧ d c₁ ∧ ⋯ ∧ d cₚ`. -/
theorem exists_incl_eq_mon (O : Y.Opens) (b : Γ(Y, O)) (l : List Γ(Y, O)) :
    ∃ x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (l.length : ℤ)).val.obj (op O),
      (TB g).incl (l.length : ℤ) x = mon g O b l ∧
      (TB g).incl ((l.length + 1 : ℕ) : ℤ)
          (((Scheme.Hom.deRhamComplex g).d l.length (l.length + 1)).val.app (op O) x) =
        dmon g O b l := by
  set p := l.length
  let c : Fin (p + 1) → Y.sheaf.obj.obj (op O) := Fin.cons b l.get
  let w := (TB g).homogeneousProdLeft (op O) p fun i =>
    SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras g) (op O) (c i.succ)
  refine ⟨c 0 • w, ?_, ?_⟩
  · refine ((sm_mul_incl (g := g) b _ w).symm).trans ?_
    refine congrArg (sm g O b * ·) ?_
    refine ((TB g).incl_homogeneousProdLeft (op O) p _).trans ?_
    rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  · have h := Scheme.Hom.deRhamComplex_d_homogeneousProdLeft g (op O) p c
    refine (congrArg ((TB g).incl ((p + 1 : ℕ) : ℤ)) h).trans ?_
    refine ((TB g).incl_homogeneousProdLeft (op O) (p + 1) _).trans ?_
    rw [List.ofFn_succ, List.prod_cons]
    refine congrArg (δ g O b * ·) ?_
    rw [← List.ofFn_get l, List.map_ofFn]
    rfl

/-- Moving `dc` past a wedge `dc₁ ∧ ⋯ ∧ dc_p` of exact one-forms multiplies by `(-1)^p`. -/
theorem δ_mul_list_prod {O : Y.Opens} (c : Γ(Y, O)) (l : List Γ(Y, O)) :
    δ g O c * (l.map (δ g O)).prod = (-1) ^ l.length * ((l.map (δ g O)).prod * δ g O c) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [← mul_assoc, δ_anticomm, neg_mul, mul_assoc, ih]
    simp only [mul_neg, neg_mul, mul_one, mul_assoc]
    rw [← mul_assoc (δ g O a), ← ((Commute.neg_one_left (δ g O a)).pow_left l.length).eq,
      mul_assoc]

/-- The product of `b · dc₁ ∧ ⋯ ∧ dc_p` and `b' · dc'₁ ∧ ⋯ ∧ dc'_q` is
`bb' · dc₁ ∧ ⋯ ∧ dc_p ∧ dc'₁ ∧ ⋯ ∧ dc'_q`. -/
theorem mon_mul {O : Y.Opens} (b b' : Γ(Y, O)) (l l' : List Γ(Y, O)) :
    mon g O b l * mon g O b' l' = mon g O (b * b') (l ++ l') := by
  simp only [mon, List.map_append, List.prod_append, map_mul]
  rw [mul_assoc, ← mul_assoc _ (sm g O b'), ← sm_comm, mul_assoc, mul_assoc]

/-- The graded Leibniz rule `d(m m') = dm · m' + (-1)^p m · dm'` for `m = b · dc₁ ∧ ⋯ ∧ dc_p` and
`m' = b' · dc'₁ ∧ ⋯ ∧ dc'_q`. -/
theorem dmon_mul {O : Y.Opens} (b b' : Γ(Y, O)) (l l' : List Γ(Y, O)) :
    dmon g O (b * b') (l ++ l') =
      dmon g O b l * mon g O b' l' + (-1) ^ l.length * (mon g O b l * dmon g O b' l') := by
  have e1 : δ g O b * (l.map (δ g O)).prod * (sm g O b' * (l'.map (δ g O)).prod) =
      sm g O b' * δ g O b * ((l.map (δ g O)).prod * (l'.map (δ g O)).prod) := by
    rw [mul_assoc, ← mul_assoc (l.map (δ g O)).prod, ← sm_comm, mul_assoc, ← mul_assoc,
      ← sm_comm]
  have e2 : sm g O b * δ g O b' * ((l.map (δ g O)).prod * (l'.map (δ g O)).prod) =
      (-1) ^ l.length * (sm g O b * (l.map (δ g O)).prod * (δ g O b' *
      (l'.map (δ g O)).prod)) := by
    rw [mul_assoc (sm g O b), ← mul_assoc (δ g O b') (l.map (δ g O)).prod,
      δ_mul_list_prod b' l]
    simp only [mul_assoc]
    rw [← mul_assoc (sm g O b), ← ((Commute.neg_one_left (sm g O b)).pow_left l.length).eq,
      mul_assoc]
  simp only [dmon, mon, δ_mul, List.map_append, List.prod_append, add_mul]
  rw [e1, ← e2, add_comm]

/-- The degree-`i` component of a homogeneous element of degree `j ≠ i` is zero. -/
theorem proj_incl_of_ne {O : Y.Opens} {i j : ℤ} (h : j ≠ i)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece j).val.obj (op O)) :
    (TB g).proj (op O) i ((TB g).incl j x) = 0 :=
  DirectSum.of_eq_of_ne _ _ _ h.symm

/-- The de Rham differential in degree `p`, applied to the degree-`p` component of an element of
the total ring and read back in the total ring. -/
noncomputable def Δ (g : Y ⟶ S) (O : Y.Opens) (p : ℕ) :
    (TB g).Total (op O) →+ (TB g).Total (op O) where
  toFun z := (TB g).incl ((p + 1 : ℕ) : ℤ)
    (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op O) ((TB g).proj (op O) p z))
  map_zero' := by
    rw [map_zero]
    exact (congrArg ((TB g).incl _) (map_zero _)).trans ((TB g).incl_zero _)
  map_add' z z' := by
    rw [map_add]
    exact (congrArg ((TB g).incl _) (map_add _ _ _)).trans ((TB g).incl_add _ _ _)

/-- On a `p`-form, `Δ g O p` is the de Rham differential. -/
theorem Δ_incl {O : Y.Opens} (p : ℕ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    Δ g O p ((TB g).incl (p : ℤ) x) = (TB g).incl ((p + 1 : ℕ) : ℤ)
      (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op O) x) := by
  change (TB g).incl _ (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op O)
    ((TB g).proj (op O) p ((TB g).incl (p : ℤ) x))) = _
  rw [(TB g).proj_incl]

/-- `Δ g O p` sends `b · dc₁ ∧ ⋯ ∧ dc_q` to `db ∧ dc₁ ∧ ⋯ ∧ dc_q` if `q = p`, and to zero
otherwise. -/
theorem Δ_mon {O : Y.Opens} (p : ℕ) (b : Γ(Y, O)) (l : List Γ(Y, O)) :
    Δ g O p (mon g O b l) = if l.length = p then dmon g O b l else 0 := by
  obtain ⟨x, hx, hdx⟩ := exists_incl_eq_mon (g := g) O b l
  rw [← hx]
  split_ifs with h
  · subst h
    rw [Δ_incl, hdx]
  · change (TB g).incl _ (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op O)
      ((TB g).proj (op O) p ((TB g).incl (l.length : ℤ) x))) = 0
    rw [proj_incl_of_ne (by exact_mod_cast h)]
    exact (congrArg ((TB g).incl _) (map_zero _)).trans ((TB g).incl_zero _)

/-- **The differential preserves the forms generated by functions, exact forms and forms
`b · d c₁ ∧ ⋯ ∧ d cₚ` whose differential they contain.** Let `G` be a set of products
`b · d c₁ ∧ ⋯ ∧ d cₚ` whose differentials `d b ∧ d c₁ ∧ ⋯ ∧ d cₚ` lie in the ring generated by `G`,
and let `J` be a set of functions whose differentials are multiples of elements of `J` by
elements of that ring. Then the de Rham differential maps the `J`-multiples of the ring
generated by `G` to themselves, degree by degree. -/
theorem Δ_mem_closure {O : Y.Opens} (G : Set ((TB g).Total (op O)))
    (hG : ∀ z ∈ G, ∃ b l, z = mon g O b l ∧ dmon g O b l ∈ Subring.closure G)
    {A : Type*} (ρ : A → Γ(Y, O)) (J : Set A)
    (hJ : ∀ c ∈ J, ∃ c₀ ∈ J, ∃ ω ∈ Subring.closure G, δ g O (ρ c) = sm g O (ρ c₀) * ω)
    (p : ℕ) {z : (TB g).Total (op O)}
    (hz : z ∈ AddSubgroup.closure
      {η | ∃ c ∈ J, ∃ ζ ∈ Subring.closure G, η = sm g O (ρ c) * ζ}) :
    Δ g O p z ∈ AddSubgroup.closure
      {η | ∃ c ∈ J, ∃ ζ ∈ Subring.closure G, η = sm g O (ρ c) * ζ} := by
  set R₀ := Subring.closure G
  set Z := AddSubgroup.closure {η | ∃ c ∈ J, ∃ ζ ∈ R₀, η = sm g O (ρ c) * ζ}
  let M : Submonoid ((TB g).Total (op O)) :=
    { carrier := {z | ∃ b l, z = mon g O b l ∧ mon g O b l ∈ R₀ ∧ dmon g O b l ∈ R₀}
      one_mem' := ⟨1, [], by simp [mon], by simp [mon, R₀.one_mem],
        by simp [dmon, δ_one, R₀.zero_mem]⟩
      mul_mem' := by
        rintro _ _ ⟨b, l, rfl, hm, hd⟩ ⟨b', l', rfl, hm', hd'⟩
        refine ⟨b * b', l ++ l', mon_mul b b' l l', ?_, ?_⟩
        · rw [← mon_mul]; exact R₀.mul_mem hm hm'
        · rw [dmon_mul]
          exact R₀.add_mem (R₀.mul_mem hd hm') (R₀.mul_mem (R₀.pow_mem (R₀.neg_mem R₀.one_mem) _)
            (R₀.mul_mem hm hd')) }
  have hGM : Submonoid.closure G ≤ M := by
    refine Submonoid.closure_le.mpr fun z hz => ?_
    obtain ⟨b, l, rfl, hd⟩ := hG z hz
    exact ⟨b, l, rfl, Subring.subset_closure hz, hd⟩
  have hR₀ : ∀ ζ ∈ R₀, ζ ∈ AddSubgroup.closure (M : Set ((TB g).Total (op O))) := fun ζ hζ =>
    AddSubgroup.closure_mono hGM (Subring.mem_closure_iff.mp hζ)
  have hgen : ∀ c ∈ J, ∀ ζ ∈ R₀, Δ g O p (sm g O (ρ c) * ζ) ∈ Z := by
    intro c hc ζ hζ
    obtain ⟨c₀, hc₀, ω, hω, hδc⟩ := hJ c hc
    have hζ' := hR₀ ζ hζ
    clear hζ
    induction hζ' using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨b, l, rfl, hm, hd⟩ := hz
      have e : sm g O (ρ c) * mon g O b l = mon g O (ρ c * b) l := by
        simp only [mon, map_mul, mul_assoc]
      rw [e, Δ_mon]
      split_ifs
      · have e2 : dmon g O (ρ c * b) l =
            sm g O (ρ c) * dmon g O b l + sm g O (ρ c₀) * (ω * mon g O b l) := by
          simp only [dmon, mon, δ_mul, add_mul, hδc]
          rw [show sm g O b * (sm g O (ρ c₀) * ω) = sm g O (ρ c₀) * (ω * sm g O b) by
            rw [← mul_assoc, sm_comm (c := b) (sm g O (ρ c₀)), mul_assoc, sm_comm (c := b) ω]]
          simp only [mul_assoc]
        rw [e2]
        exact Z.add_mem (AddSubgroup.subset_closure ⟨c, hc, _, hd, rfl⟩)
          (AddSubgroup.subset_closure ⟨c₀, hc₀, _, R₀.mul_mem hω hm, rfl⟩)
      · exact Z.zero_mem
    | zero => rw [mul_zero, map_zero]; exact Z.zero_mem
    | add z z' _ _ hz hz' => rw [mul_add, map_add]; exact Z.add_mem hz hz'
    | neg z _ hz => rw [mul_neg, map_neg]; exact Z.neg_mem hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, ζ, hζ, rfl⟩ := hz
    exact hgen c hc ζ hζ
  | zero => rw [map_zero]; exact Z.zero_mem
  | add z z' _ _ hz hz' => rw [map_add]; exact Z.add_mem hz hz'
  | neg z _ hz => rw [map_neg]; exact Z.neg_mem hz

/-- If `st = 1` then `ds ∧ dt = 0`. -/
theorem δ_mul_δ_of_mul_eq_one {O : Y.Opens} {s t : Γ(Y, O)} (h : s * t = 1) :
    δ g O s * δ g O t = 0 := by
  have h1 : sm g O t * δ g O s = -(sm g O s * δ g O t) := by
    refine eq_neg_of_add_eq_zero_right ?_
    rw [← δ_mul, h, δ_one]
  calc δ g O s * δ g O t = sm g O (s * t) * (δ g O s * δ g O t) := by rw [h, map_one, one_mul]
    _ = sm g O s * ((sm g O t * δ g O s) * δ g O t) := by rw [map_mul, mul_assoc, mul_assoc]
    _ = 0 := by rw [h1, neg_mul, mul_assoc, δ_mul_self, mul_zero, neg_zero, mul_zero]

/-- **The logarithmic derivative of a product.** If each `aᵢ` has an inverse `sᵢ`, then
`d(∏ aᵢ) = (∏ aᵢ) · ∑ sᵢ daᵢ`. -/
theorem δ_prod_eq {O : Y.Opens} {r : ℕ} (a s : Fin r → Γ(Y, O)) (hs : ∀ i, s i * a i = 1) :
    δ g O (∏ i, a i) = sm g O (∏ i, a i) * ∑ i, sm g O (s i) * δ g O (a i) := by
  induction r with
  | zero => simp [δ_one]
  | succ r ih =>
    set P := ∏ i : Fin r, a i.succ
    have e2 : sm g O P * δ g O (a 0) = sm g O (a 0) * sm g O P * (sm g O (s 0) * δ g O (a 0)) := by
      rw [← mul_assoc, ← map_mul, ← map_mul,
        show a 0 * P * s 0 = P by rw [mul_comm (a 0), mul_assoc, mul_comm (a 0), hs 0, mul_one]]
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, δ_mul, ih (fun i => a i.succ) (fun i => s i.succ)
      (fun i => hs i.succ), map_mul, mul_add, ← mul_assoc (sm g O (a 0)), e2, add_comm]

/-- `incl` commutes with finite sums. -/
theorem incl_sum {O : Y.Opens} (p : ℤ) {ι : Type*} (s : Finset ι)
    (x : ι → ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.obj (op O)) :
    (TB g).incl p (∑ i ∈ s, x i) = ∑ i ∈ s, (TB g).incl p (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (TB g).incl_zero p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact (TB g).incl_add p _ _

/-- `ι1` commutes with finite sums. -/
theorem ι1_sum {O : Y.Opens} {ι : Type*} (s : Finset ι)
    (ξ : ι → (Scheme.Hom.relativeDifferentials g).val.obj (op O)) :
    ι1 g O (∑ i ∈ s, ξ i) = ∑ i ∈ s, ι1 g O (ξ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (congrArg ((TB g).incl 1) (map_zero _)).trans ((TB g).incl_zero _)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ι1_add, ih]

/-- The list of values of `s.orderEmbOfFin h` is the increasing enumeration of `s`. -/
theorem ofFn_orderEmbOfFin {α : Type*} [LinearOrder α] (s : Finset α) {p : ℕ}
    (h : s.card = p) : List.ofFn (fun i => s.orderEmbOfFin h i) = s.sort (· ≤ ·) := by
  rw [List.ofFn_eq_map]; exact Finset.listMap_orderEmbOfFin_finRange s h

/-- A product of terms `σᵢ xᵢ` with functions `σᵢ` is `(∏ σᵢ) · ∏ xᵢ`. -/
theorem prod_map_sm_mul {O : Y.Opens} {ι : Type*} (σ : ι → Γ(Y, O))
    (x : ι → (TB g).Total (op O)) (l : List ι) :
    (l.map fun i => sm g O (σ i) * x i).prod = sm g O (l.map σ).prod * (l.map x).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih, map_mul]
    rw [mul_assoc, ← mul_assoc (x a), ← sm_comm, mul_assoc, mul_assoc]

/-- **Wedges of a basis of exact forms are independent.** On an affine open `O` of `Y`, over an
affine open of `S`, if `dτ₁, …, dτₙ` is a basis of the Kähler differentials, then the wedges
`dτ_K`, `K` a `p`-element subset, are linearly independent over `Γ(Y, O)` in the total ring of
forms. -/
theorem eq_zero_of_sum_sm_mul_prod_eq_zero {O : Y.Opens} (hO : IsAffineOpen O)
    {V : S.Opens} (hV : IsAffineOpen V) (e : O ≤ g ⁻¹ᵁ V) {n : ℕ} (τ : Fin n → Γ(Y, O))
    (hb : letI := (g.appLE V O e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(Y, O) Ω[Γ(Y, O)⁄Γ(S, V)],
        ∀ i, b i = KaehlerDifferential.D Γ(S, V) Γ(Y, O) (τ i))
    (p : ℕ) (a : {K : Finset (Fin n) // K.card = p} → Γ(Y, O))
    (ha : ∑ K, sm g O (a K) * ((K.1.sort (· ≤ ·)).map fun i => δ g O (τ i)).prod = 0) :
    a = 0 := by
  let _ := (g.appLE V O e).hom.toAlgebra
  obtain ⟨b, hb⟩ := hb
  have := Scheme.Hom.isQuasicoherent_relativeDifferentials g
  let kE := Stacks.AlgebraicGeometry.AffineOpenDeRham.kaehlerSectionsEquiv g hO hV e
  let b₁ := b.map kE
  have hb₁ : ∀ i, b₁ i = (Scheme.Hom.universalRelativeDerivation g).d (X := op O) (τ i) :=
    fun i => (congrArg kE (hb i)).trans
      (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d g V O e (τ i))
  let iso := Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso
    (Scheme.Hom.relativeDifferentials g) hO
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (Scheme.Hom.relativeDifferentials g)) p
  let z : {K : Finset (Fin n) // K.card = p} →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O) :=
    fun K => (TB g).homogeneousProd (op O) p fun k =>
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials g)).val.app (op O)
        (b₁ (K.1.orderEmbOfFin K.2 k))
  have hz : ∀ K, (TB g).incl (p : ℤ) (z K) =
      ((K.1.sort (· ≤ ·)).map fun i => δ g O (τ i)).prod := fun K => by
    refine ((TB g).incl_homogeneousProd (op O) p _).trans ?_
    rw [← ofFn_orderEmbOfFin K.1 K.2, List.map_ofFn]
    exact congrArg (fun F => (List.ofFn F).prod) (funext fun k => congrArg (ι1 g O) (hb₁ _))
  have hiso : ∀ K, iso.hom.hom (z K) = exteriorPower.ιMulti_family Γ(Y, O) p b₁ K := fun K =>
    Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso_hom_homogeneousProd _ hO _ p _
  let a' : {K : Finset (Fin n) // K.card = p} →
      (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O) := a
  have hsum : ∑ K, a' K • z K = 0 := by
    refine (TB g).incl_inj_of_proj ?_
    rw [(TB g).incl_zero, ← ha]
    simp only [← hz]
    rw [incl_sum]
    exact Finset.sum_congr rfl fun K _ => (sm_mul_incl (a K) _ (z K)).symm
  have hsum' : ∑ K : {K : Finset (Fin n) // K.card = p},
      a K • exteriorPower.ιMulti_family Γ(Y, O) p b₁ K = 0 := by
    have h1 := congrArg iso.hom.hom hsum
    have h2 : iso.hom.hom (∑ K, a' K • z K) = ∑ K, a K • iso.hom.hom (z K) :=
      (map_sum iso.hom.hom _ _).trans (Finset.sum_congr rfl fun K _ => iso.hom.hom.map_smul _ _)
    have h3 : ∑ K, a K • iso.hom.hom (z K) = 0 := h2.symm.trans (h1.trans (map_zero _))
    refine Eq.trans ?_ h3
    exact Finset.sum_congr rfl fun K _ => by rw [hiso]
  have hli := exteriorPower.ιMulti_family_linearIndependent_ofBasis Γ(Y, O) p b₁
  funext K
  exact linearIndependent_iff'.mp hli (Finset.univ : Finset {K : Finset (Fin n) // K.card = p})
    a hsum' K (Finset.mem_univ K)

/-- Sections of a sheaf of forms agreeing on the members of an open cover are equal. -/
theorem piece_ext (p : ℤ) {O : Y.Opens} {ι : Type*} (Ox : ι → Y.Opens) (ix : ∀ i, Ox i ⟶ O)
    (hcov : O ≤ iSup Ox)
    (x y : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.obj (op O))
    (h : ∀ i, ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.map (ix i).op x =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.map (ix i).op y) :
    x = y := by
  let Sv : Sieve O :=
    { arrows := fun V _ => ∃ i, V ≤ Ox i
      downward_closed := fun {_ _} {_} hi g => by
        obtain ⟨i, hi⟩ := hi
        exact ⟨i, (leOfHom g).trans hi⟩ }
  have hS : Sv ∈ Opens.grothendieckTopology Y O := by
    intro z hz
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hz)
    exact ⟨Ox i, ix i, ⟨i, le_rfl⟩, hi⟩
  refine ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).isSheaf.isSeparated O Sv hS
    x y fun V φ ⟨i, hi⟩ => ?_
  have hφ : φ = homOfLE hi ≫ ix i := Subsingleton.elim _ _
  subst hφ
  change ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.map
      ((ix i).op ≫ (homOfLE hi).op) x =
    ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.map
      ((ix i).op ≫ (homOfLE hi).op) y
  rw [PresheafOfModules.map_comp_apply, PresheafOfModules.map_comp_apply, h i]

end Forms

/-! ### Twisted differentials `d - θ ∧` on the forms of a scheme -/

section Twisted

variable {Y S : Scheme.{u}} {g : Y ⟶ S}

/-- `incl` of a section transported along an equality of degrees. -/
theorem incl_proj_of_eq {O : Y.Opens} {i j : ℤ} (h : i = j)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece i).val.obj (op O)) :
    (TB g).incl j ((TB g).proj (op O) j ((TB g).incl i x)) = (TB g).incl i x := by
  subst h
  rw [(TB g).proj_incl]

variable (g) in
/-- The wedge `θ ∧ ω` of a one-form with a `p`-form, a `(p + 1)`-form. -/
noncomputable def wedgeOne {O : Y.Opens} (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece ((p + 1 : ℕ) : ℤ)).val.obj (op O) :=
  (TB g).proj (op O) ((p + 1 : ℕ) : ℤ) ((TB g).incl 1 θ * (TB g).incl (p : ℤ) ω)

/-- In the total ring of forms, `θ ∧ ω` is the product of `θ` and `ω`. -/
theorem incl_wedgeOne {O : Y.Opens} (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    (TB g).incl ((p + 1 : ℕ) : ℤ) (wedgeOne g p θ ω) = (TB g).incl 1 θ * (TB g).incl (p : ℤ) ω := by
  unfold wedgeOne
  rw [(TB g).incl_mul_incl]
  exact incl_proj_of_eq (by push_cast; ring) _

variable (g) in
/-- The twisted differential `∇ω = dω - θ ∧ ω` of a `p`-form. -/
noncomputable def nab {O : Y.Opens} (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece ((p + 1 : ℕ) : ℤ)).val.obj (op O) :=
  (show ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece ((p + 1 : ℕ) : ℤ)).val.obj (op O)
    from ((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op O) ω) - wedgeOne g p θ ω

/-- `incl` commutes with subtraction. -/
theorem incl_sub {O : Y.Opens} (p : ℤ)
    (x y : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.obj (op O)) :
    (TB g).incl p (x - y) = (TB g).incl p x - (TB g).incl p y := by
  rw [eq_sub_iff_add_eq, ← (TB g).incl_add, sub_add_cancel]

/-- In the total ring of forms, `∇ω = dω - θ ω`. -/
theorem incl_nab {O : Y.Opens} (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    (TB g).incl ((p + 1 : ℕ) : ℤ) (nab g p θ ω) =
      Δ g O p ((TB g).incl (p : ℤ) ω) - (TB g).incl 1 θ * (TB g).incl (p : ℤ) ω := by
  unfold nab
  rw [incl_sub, Δ_incl, ← incl_wedgeOne]

/-- `b · dc₁ ∧ ⋯ ∧ dc_p` is homogeneous of degree `p`. -/
theorem mon_homogeneous {O : Y.Opens} (b : Γ(Y, O)) (l : List Γ(Y, O)) :
    ∃ x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (l.length : ℤ)).val.obj (op O),
      (TB g).incl (l.length : ℤ) x = mon g O b l :=
  let ⟨x, hx, _⟩ := exists_incl_eq_mon (g := g) O b l
  ⟨x, hx⟩

/-- The degree-`q` component of `b · dc₁ ∧ ⋯ ∧ dc_p` vanishes for `q ≠ p`. -/
theorem proj_mon_of_ne {O : Y.Opens} (b : Γ(Y, O)) (l : List Γ(Y, O)) {p : ℕ}
    (h : l.length ≠ p) : (TB g).proj (op O) (p : ℤ) (mon g O b l) = 0 := by
  obtain ⟨x, hx⟩ := mon_homogeneous (g := g) b l
  rw [← hx]
  exact proj_incl_of_ne (by exact_mod_cast h) x

/-- `b · dc₁ ∧ ⋯ ∧ dc_p` equals its degree-`p` component. -/
theorem incl_proj_mon {O : Y.Opens} (b : Γ(Y, O)) (l : List Γ(Y, O)) :
    (TB g).incl (l.length : ℤ) ((TB g).proj (op O) (l.length : ℤ) (mon g O b l)) = mon g O b l := by
  obtain ⟨x, hx⟩ := mon_homogeneous (g := g) b l
  rw [← hx, (TB g).proj_incl]

variable (g) in
/-- The twisted differential `z ↦ dz_p - θ ∧ z_p` on the degree-`p` part of a section of the total
ring of forms. -/
noncomputable def twT (O : Y.Opens) (p : ℕ) (θ : (TB g).Total (op O)) :
    (TB g).Total (op O) →+ (TB g).Total (op O) where
  toFun z := Δ g O p z - θ * (TB g).incl (p : ℤ) ((TB g).proj (op O) (p : ℤ) z)
  map_zero' := by
    rw [map_zero, map_zero, (TB g).incl_zero, mul_zero, sub_zero]
  map_add' z z' := by
    rw [map_add, map_add, (TB g).incl_add, mul_add]
    abel

/-- `twT g O p θ z = dz_p - θ z_p`. -/
theorem twT_apply {O : Y.Opens} (p : ℕ) (θ z : (TB g).Total (op O)) :
    twT g O p θ z = Δ g O p z - θ * (TB g).incl (p : ℤ) ((TB g).proj (op O) (p : ℤ) z) := rfl

/-- On a `p`-form, `twT` is the twisted differential `nab`. -/
theorem twT_incl {O : Y.Opens} (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    twT g O p ((TB g).incl 1 θ) ((TB g).incl (p : ℤ) ω) =
      (TB g).incl ((p + 1 : ℕ) : ℤ) (nab g p θ ω) := by
  rw [twT_apply, (TB g).proj_incl, incl_nab]

/-- `twT g O p θ` sends `m = b · dc₁ ∧ ⋯ ∧ dc_q` to `dm - θ m` if `q = p`, and to `0` otherwise. -/
theorem twT_mon {O : Y.Opens} (p : ℕ) (θ : (TB g).Total (op O)) (b : Γ(Y, O))
    (l : List Γ(Y, O)) :
    twT g O p θ (mon g O b l) = if l.length = p then dmon g O b l - θ * mon g O b l else 0 := by
  rw [twT_apply, Δ_mon]
  split_ifs with h
  · subst h
    rw [incl_proj_mon]
  · rw [proj_mon_of_ne b l h, (TB g).incl_zero, mul_zero, sub_zero]

/-- `db ∧ dc₁ ∧ ⋯ ∧ dc_p` is `1 · db ∧ dc₁ ∧ ⋯ ∧ dc_p`. -/
theorem dmon_eq_mon {O : Y.Opens} (b : Γ(Y, O)) (l : List Γ(Y, O)) :
    dmon g O b l = mon g O 1 (b :: l) := by
  simp only [dmon, mon, map_one, one_mul, List.map_cons, List.prod_cons]

/-- `c du · (b · dc₁ ∧ ⋯ ∧ dc_p) = cb · du ∧ dc₁ ∧ ⋯ ∧ dc_p`. -/
theorem sm_mul_δ_mul_mon {O : Y.Opens} (c u b : Γ(Y, O)) (l : List Γ(Y, O)) :
    sm g O c * δ g O u * mon g O b l = mon g O (c * b) (u :: l) := by
  simp only [mon, map_mul, List.map_cons, List.prod_cons, mul_assoc]
  congr 1
  rw [← mul_assoc, ← sm_comm b (δ g O u), mul_assoc]

/-- **The twisted differential squares to zero on products.** If `θ = c · du` with
`dc ∧ du = 0`, then `∇(∇(b · dc₁ ∧ ⋯ ∧ dc_p)) = 0`. -/
theorem twT_twT_mon {O : Y.Opens} (p : ℕ) (c u : Γ(Y, O))
    (hcu : δ g O c * δ g O u = 0) (b : Γ(Y, O)) (l : List Γ(Y, O)) :
    twT g O (p + 1) (sm g O c * δ g O u) (twT g O p (sm g O c * δ g O u) (mon g O b l)) = 0 := by
  rw [twT_mon]
  split_ifs with h
  · rw [map_sub, dmon_eq_mon, sm_mul_δ_mul_mon, twT_mon, twT_mon]
    have h1 : (b :: l).length = p + 1 := by simp [h]
    have h2 : (u :: l).length = p + 1 := by simp [h]
    rw [ite_eq_left h1, ite_eq_left h2]
    have e1 : dmon g O 1 (b :: l) = 0 := by simp [dmon, δ_one]
    have e2 : sm g O c * δ g O u * mon g O (c * b) (u :: l) = 0 := by
      simp only [mon, List.map_cons, List.prod_cons]
      rw [mul_assoc, ← mul_assoc (δ g O u), ← sm_comm (c * b) (δ g O u),
        mul_assoc (sm g O (c * b)), ← mul_assoc (δ g O u) (δ g O u), δ_mul_self, zero_mul,
        mul_zero, mul_zero]
    set P := (l.map (δ g O)).prod
    have e3 : sm g O c * δ g O u * mon g O 1 (b :: l) = -(sm g O c * δ g O b * (δ g O u * P)) := by
      simp only [mon, List.map_cons, List.prod_cons, map_one, one_mul]
      rw [mul_assoc, ← mul_assoc (δ g O u), δ_anticomm u b, neg_mul, mul_neg, ← mul_assoc]
      simp only [P, mul_assoc]
    have e4 : dmon g O (c * b) (u :: l) =
        sm g O c * δ g O b * (δ g O u * P) + sm g O b * (δ g O c * δ g O u) * P := by
      simp only [dmon, List.map_cons, List.prod_cons, δ_mul, add_mul]
      simp only [P, mul_assoc]
    rw [e1, e2, e3, e4, hcu, mul_zero, zero_mul, add_zero]
    abel
  · exact map_zero _

variable (g) in
/-- The additive subgroup of the total ring of forms over `O` generated by the products
`b · dc₁ ∧ ⋯ ∧ dc_p`. -/
noncomputable def monSet (O : Y.Opens) : AddSubgroup ((TB g).Total (op O)) :=
  AddSubgroup.closure {z | ∃ b l, z = mon g O b l}

/-- Every product `b · dc₁ ∧ ⋯ ∧ dc_p` lies in `monSet`. -/
theorem mon_mem_monSet {O : Y.Opens} (b : Γ(Y, O)) (l : List Γ(Y, O)) :
    mon g O b l ∈ monSet g O :=
  AddSubgroup.subset_closure ⟨b, l, rfl⟩

/-- `∇ ∘ ∇ = 0` on the sums of products `b · dc₁ ∧ ⋯ ∧ dc_p`. -/
theorem twT_twT_of_mem {O : Y.Opens} (p : ℕ) (c u : Γ(Y, O))
    (hcu : δ g O c * δ g O u = 0) {z : (TB g).Total (op O)} (hz : z ∈ monSet g O) :
    twT g O (p + 1) (sm g O c * δ g O u) (twT g O p (sm g O c * δ g O u) z) = 0 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, l, rfl⟩ := hz
    exact twT_twT_mon p c u hcu b l
  | zero => rw [map_zero, map_zero]
  | add z z' _ _ hz hz' => rw [map_add, map_add, hz, hz', add_zero]
  | neg z _ hz => rw [map_neg, map_neg, hz, neg_zero]

/-- `monSet` is closed under multiplication. -/
theorem mul_mem_monSet {O : Y.Opens} {z z' : (TB g).Total (op O)} (hz : z ∈ monSet g O)
    (hz' : z' ∈ monSet g O) : z * z' ∈ monSet g O := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, l, rfl⟩ := hz
    induction hz' using AddSubgroup.closure_induction with
    | mem z' hz' =>
      obtain ⟨b', l', rfl⟩ := hz'
      rw [mon_mul]
      exact mon_mem_monSet _ _
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

/-- Functions lie in `monSet`. -/
theorem sm_mem_monSet {O : Y.Opens} (a : Γ(Y, O)) : sm g O a ∈ monSet g O := by
  have : sm g O a = mon g O a [] := by simp [mon]
  rw [this]
  exact mon_mem_monSet _ _

/-- Exact one-forms lie in `monSet`. -/
theorem δ_mem_monSet {O : Y.Opens} (a : Γ(Y, O)) : δ g O a ∈ monSet g O := by
  have : δ g O a = mon g O 1 [a] := by simp [mon]
  rw [this]
  exact mon_mem_monSet _ _

/-- The restriction of `b · dc₁ ∧ ⋯ ∧ dc_p` is the product of the restrictions of `b` and of the
`cᵢ`. -/
theorem totalRestrict_mon {O O' : Y.Opens} (φ : op O ⟶ op O') (b : Γ(Y, O))
    (l : List Γ(Y, O)) :
    (TB g).totalRestrict φ (mon g O b l) = mon g O' (Y.presheaf.map φ b) (l.map (Y.presheaf.map
        φ)) := by
  have hR : ∀ z, (TB g).totalRestrictRingHom φ z = (TB g).totalRestrict φ z := fun z =>
    (TB g).totalRestrictRingHom_apply φ z
  rw [← hR]
  simp only [mon, map_mul, map_list_prod, List.map_map]
  rw [hR, totalRestrict_sm]
  congr 2
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp_apply]
  rw [hR, totalRestrict_δ]

/-- Restriction maps `monSet` into `monSet`. -/
theorem totalRestrict_mem_monSet {O O' : Y.Opens} (φ : op O ⟶ op O')
    {z : (TB g).Total (op O)} (hz : z ∈ monSet g O) :
    (TB g).totalRestrict φ z ∈ monSet g O' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, l, rfl⟩ := hz
    rw [totalRestrict_mon]
    exact mon_mem_monSet _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/-- The de Rham differential commutes with restriction. -/
theorem deRham_map {O O' : Y.Opens} (φ : op O ⟶ op O') (p : ℕ)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    ((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op O')
        (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.map φ ω) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece ((p + 1 : ℕ) : ℤ)).val.map φ
        (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op O) ω) :=
  PresheafOfModules.naturality_apply ((Scheme.Hom.deRhamComplex g).d p (p + 1)).val φ ω

/-- The twisted differential commutes with restriction. -/
theorem nab_map {O O' : Y.Opens} (φ : op O ⟶ op O') (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece ((p + 1 : ℕ) : ℤ)).val.map φ
        (nab g p θ ω) =
      nab g p (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.map φ θ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.map φ ω) := by
  refine (TB g).incl_inj_of_proj ?_
  have hR : ∀ z, (TB g).totalRestrictRingHom φ z = (TB g).totalRestrict φ z := fun z =>
    (TB g).totalRestrictRingHom_apply φ z
  have e : ∀ (i : ℤ) (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece i).val.obj (op O)),
      (TB g).incl i (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece i).val.map φ x) =
        (TB g).totalRestrict φ ((TB g).incl i x) := fun i x =>
    ((TB g).totalRestrict_incl φ i x).symm
  refine (e _ _).trans ?_
  refine Eq.trans ?_ (incl_nab p _ _).symm
  have h1 : Δ g O' p ((TB g).incl (p : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.map φ ω)) =
      (TB g).totalRestrict φ ((TB g).incl ((p + 1 : ℕ) : ℤ)
        (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op O) ω)) :=
    (Δ_incl p _).trans ((congrArg ((TB g).incl _) (deRham_map φ p ω)).trans (e _ _))
  have h2 : (TB g).incl 1 (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.map φ θ) *
      (TB g).incl (p : ℤ) (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.map
          φ ω) =
      (TB g).totalRestrict φ ((TB g).incl 1 θ * (TB g).incl (p : ℤ) ω) := by
    refine (congrArg₂ (· * ·) (e _ _) (e _ _)).trans ?_
    rw [← hR, ← hR, ← hR, map_mul]
  refine Eq.trans ?_ (congrArg₂ (· - ·) h1.symm h2.symm)
  rw [incl_nab, Δ_incl]
  exact map_sub _ _ _

/-- The twisted differential is additive. -/
theorem nab_add {O : Y.Opens} (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (ω ω' : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    nab g p θ (ω + ω') = nab g p θ ω + nab g p θ ω' := by
  refine (TB g).incl_inj_of_proj ?_
  rw [(TB g).incl_add, incl_nab, incl_nab, incl_nab, (TB g).incl_add, map_add, mul_add]
  abel

/-- `∇ ∘ ∇ = 0` on a form which is a sum of products `b · dc₁ ∧ ⋯ ∧ dc_p`, when `θ = c · du` with
`dc ∧ du = 0`. -/
theorem nab_nab_of_mem {O : Y.Opens} (p : ℕ) (c u : Γ(Y, O))
    (hcu : δ g O c * δ g O u = 0)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (hθ : (TB g).incl 1 θ = sm g O c * δ g O u)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O))
    (hω : (TB g).incl (p : ℤ) ω ∈ monSet g O) :
    nab g (p + 1) θ (nab g p θ ω) = 0 := by
  refine (TB g).incl_inj_of_proj ?_
  rw [(TB g).incl_zero, ← twT_incl, ← twT_incl, hθ]
  exact twT_twT_of_mem p c u hcu hω

/-- The wedge with a one-form is linear over functions. -/
theorem wedgeOne_smul {O : Y.Opens} (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (r : (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    wedgeOne g p θ (r • ω) = r • wedgeOne g p θ ω := by
  refine (TB g).incl_inj_of_proj ?_
  rw [incl_wedgeOne, (TB g).incl_smul, (TB g).incl_smul, incl_wedgeOne, (TB g).mul_smul_eq]

/-- The twisted differential is linear over the inverse image of the functions on the base. -/
theorem nab_smul_base {O : Y.Opens} (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj S.sheaf).obj.obj (op O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    nab g p θ ((show (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O) from
        ((inverseImageStructureMap g).hom.app (op O)).hom a) • ω) =
      (show (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O) from
        ((inverseImageStructureMap g).hom.app (op O)).hom a) • nab g p θ ω := by
  unfold nab
  rw [wedgeOne_smul, smul_sub]
  congr 1
  exact ((((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op O)).hom.map_smul a ω)

/-- `d 0 = 0`. -/
theorem δ_zero' {O : Y.Opens} : δ g O 0 = 0 := by
  have h := δ_add (g := g) (O := O) 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- The differential of a natural number is zero. -/
theorem δ_natCast {O : Y.Opens} (N : ℕ) : δ g O (N : Γ(Y, O)) = 0 := by
  induction N with
  | zero => rw [Nat.cast_zero, δ_zero']
  | succ k ih => rw [Nat.cast_succ, δ_add, ih, δ_one, add_zero]

/-- If `c · (N u) = 1` then `dc ∧ du = 0`. -/
theorem δ_mul_δ_of_mul_natCast_mul_eq_one {O : Y.Opens} {c u : Γ(Y, O)} (N : ℕ)
    (h : c * ((N : Γ(Y, O)) * u) = 1) : δ g O c * δ g O u = 0 := by
  have h0 := δ_mul_δ_of_mul_eq_one (g := g) h
  rw [δ_mul, δ_natCast, mul_zero, add_zero, ← mul_assoc, ← sm_comm (N : Γ(Y, O)) (δ g O c),
    mul_assoc] at h0
  calc δ g O c * δ g O u = sm g O (c * u * N) * (δ g O c * δ g O u) := by
        rw [show c * u * N = 1 by rw [← h]; ring, map_one, one_mul]
    _ = sm g O (c * u) * (sm g O N * (δ g O c * δ g O u)) := by rw [map_mul, mul_assoc]
    _ = 0 := by rw [h0, mul_zero]

variable (g) in
/-- `monSet` as a subring. -/
noncomputable def monSubring (O : Y.Opens) : Subring ((TB g).Total (op O)) where
  carrier := monSet g O
  mul_mem' := mul_mem_monSet
  one_mem' := by
    rw [show (1 : (TB g).Total (op O)) = mon g O 1 [] by simp [mon]]
    exact mon_mem_monSet _ _
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem

/-- Restriction in the total ring of forms is transitive. -/
theorem totalRestrict_totalRestrict {O O' O'' : Y.Opens} (φ : op O ⟶ op O')
    (ψ : op O' ⟶ op O'') (χ : op O ⟶ op O'') (z : (TB g).Total (op O)) :
    (TB g).totalRestrict ψ ((TB g).totalRestrict φ z) = (TB g).totalRestrict χ z := by
  rw [show χ = φ ≫ ψ from Subsingleton.elim _ _]
  exact (congrArg (fun F => F.hom z) ((TB g).totalPresheaf.map_comp φ ψ)).symm

/-- **The Leibniz rule on sums of products.** For `z` a sum of products
`b · dc₁ ∧ ⋯ ∧ dc_q`, `d(a z)_p = da ∧ z_p + a dz_p`. -/
theorem Δ_sm_mul {O : Y.Opens} (p : ℕ) (a : Γ(Y, O)) {z : (TB g).Total (op O)}
    (hz : z ∈ monSet g O) :
    Δ g O p (sm g O a * z) =
      δ g O a * (TB g).incl (p : ℤ) ((TB g).proj (op O) (p : ℤ) z) + sm g O a * Δ g O p z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, l, rfl⟩ := hz
    have e : sm g O a * mon g O b l = mon g O (a * b) l := by
      simp only [mon, map_mul, mul_assoc]
    rw [e, Δ_mon, Δ_mon]
    split_ifs with h
    · subst h
      rw [incl_proj_mon]
      simp only [dmon, mon, δ_mul, add_mul, mul_assoc]
      rw [add_comm, ← mul_assoc (δ g O a), ← sm_comm b (δ g O a), mul_assoc]
    · rw [proj_mon_of_ne b l h, (TB g).incl_zero, mul_zero, mul_zero, add_zero]
  | zero => simp only [mul_zero, map_zero, (TB g).incl_zero, add_zero]
  | add z z' _ _ hz hz' =>
    rw [mul_add, map_add, hz, hz', map_add, (TB g).incl_add, map_add]
    noncomm_ring
  | neg z _ hz =>
    have hn : (TB g).incl (p : ℤ) (-((TB g).proj (op O) (p : ℤ) z)) =
        -(TB g).incl (p : ℤ) ((TB g).proj (op O) (p : ℤ) z) := map_neg (DirectSum.of _ _) _
    rw [mul_neg, map_neg, hz, map_neg, map_neg, hn]
    noncomm_ring

/-- **The Leibniz rule for the twisted differential on sums of products.** -/
theorem twT_sm_mul {O : Y.Opens} (p : ℕ) (θ : (TB g).Total (op O)) (a : Γ(Y, O))
    {z : (TB g).Total (op O)} (hz : z ∈ monSet g O) :
    twT g O p θ (sm g O a * z) =
      δ g O a * (TB g).incl (p : ℤ) ((TB g).proj (op O) (p : ℤ) z) + sm g O a * twT g O p θ z := by
  rw [twT_apply, twT_apply, Δ_sm_mul p a hz]
  have e : (TB g).proj (op O) (p : ℤ) (sm g O a * z) =
      (show (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O) from a) •
        (TB g).proj (op O) (p : ℤ) z :=
    (congrArg ((TB g).proj (op O) (p : ℤ)) (smul_eq_sm_mul a z).symm).trans
      (LinearMap.map_smul _ _ _)
  rw [e, ← sm_mul_incl, mul_sub, ← mul_assoc θ, ← sm_comm a θ, mul_assoc]
  abel

/-- The computation of `∇(h g₀ · η)` from `∇ g₀ = g₀ ξ`. -/
theorem twisted_leibniz_identity {O : Y.Opens} (θ ξ z dz : (TB g).Total (op O))
    (g₀ h : Γ(Y, O)) (hξ : δ g O g₀ - θ * sm g O g₀ = sm g O g₀ * ξ) :
    δ g O (h * g₀) * z + sm g O (h * g₀) * (dz - θ * z) =
      sm g O g₀ * (sm g O h * (ξ * z) + δ g O h * z + sm g O h * dz) := by
  set A := sm g O h
  set G := sm g O g₀
  have hδ : δ g O g₀ = G * ξ + θ * G := by rw [← hξ]; abel
  have hθG : θ * G = G * θ := (sm_comm g₀ θ).symm
  have hAG : A * G = G * A := by rw [← map_mul, ← map_mul, mul_comm]
  rw [δ_mul, map_mul, hδ]
  calc (A * (G * ξ + θ * G) + G * δ g O h) * z + A * G * (dz - θ * z) =
      A * G * ξ * z + A * (θ * G) * z + G * δ g O h * z + A * G * dz - A * G * θ * z := by
        noncomm_ring
    _ = A * G * ξ * z + G * δ g O h * z + A * G * dz := by rw [hθG]; noncomm_ring
    _ = G * (A * (ξ * z) + δ g O h * z + A * dz) := by rw [hAG]; noncomm_ring

/-- **The twisted Leibniz rule on a product**: if `∇ G = G ξ` then
`∇(h G z) = G (h ξ z + dh z + h ∇z)`, for `z` a sum of products of functions and exact forms. -/
theorem twT_sm_mul_eq_of_nab {O : Y.Opens} (p : ℕ) (θ ξ : (TB g).Total (op O))
    (h' G : Γ(Y, O)) {z : (TB g).Total (op O)} (hz : z ∈ monSet g O)
    (hproj : (TB g).incl (p : ℤ) ((TB g).proj (op O) (p : ℤ) z) = z)
    (hξ : δ g O G - θ * sm g O G = sm g O G * ξ) :
    twT g O p θ (sm g O (h' * G) * z) =
      sm g O G * (sm g O h' * (ξ * z) + δ g O h' * z + sm g O h' * Δ g O p z) := by
  rw [twT_sm_mul p θ (h' * G) hz, hproj, twT_apply, hproj]
  exact twisted_leibniz_identity θ ξ z _ G h' hξ

/-- `twT_sm_mul_eq_of_nab` for `z` a form of degree `p`. -/
theorem twT_sm_mul_incl_eq_of_nab {O : Y.Opens} (p : ℕ) (θ ξ : (TB g).Total (op O))
    (h' G : Γ(Y, O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O))
    (hz : (TB g).incl (p : ℤ) ω ∈ monSet g O)
    (hξ : δ g O G - θ * sm g O G = sm g O G * ξ) :
    twT g O p θ (sm g O (h' * G) * (TB g).incl (p : ℤ) ω) =
      sm g O G * (sm g O h' * (ξ * (TB g).incl (p : ℤ) ω) + δ g O h' * (TB g).incl (p : ℤ) ω +
        sm g O h' * Δ g O p ((TB g).incl (p : ℤ) ω)) :=
  twT_sm_mul_eq_of_nab p θ ξ h' G hz (congrArg ((TB g).incl (p : ℤ)) ((TB g).proj_incl _ _ ω)) hξ

/-- One summand of the twisted differential, with every term given by an equation. -/
theorem twT_summand {O : Y.Opens} (p : ℕ) (θ ξ zr : (TB g).Total (op O)) (A h' G : Γ(Y, O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O))
    (hz : (TB g).incl (p : ℤ) ω ∈ monSet g O)
    (hξ : δ g O G - θ * sm g O G = sm g O G * ξ) (hA : A = h' * G)
    (hzr : zr = sm g O h' * (ξ * (TB g).incl (p : ℤ) ω) + δ g O h' * (TB g).incl (p : ℤ) ω +
        sm g O h' * Δ g O p ((TB g).incl (p : ℤ) ω)) :
    twT g O p θ ((TB g).structureMap (op O) A * (TB g).incl (p : ℤ) ω) =
      (TB g).structureMap (op O) G * zr := by
  rw [hA, hzr]
  exact twT_sm_mul_incl_eq_of_nab p θ ξ h' G ω hz hξ

/-- The restriction of `θ ∧ ω` is the product of the restrictions of `θ` and `ω`. -/
theorem incl_map_wedgeOne {O O' : Y.Opens} (φ : op O ⟶ op O') (p : ℕ)
    (θ : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.obj (op O))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O)) :
    (TB g).incl ((p + 1 : ℕ) : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece ((p + 1 : ℕ) : ℤ)).val.map φ
          (wedgeOne g p θ ω)) =
      (TB g).incl 1 (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece 1).val.map φ θ) *
        (TB g).incl (p : ℤ)
          (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.map φ ω) := by
  refine ((TB g).totalRestrict_incl φ _ _).symm.trans ?_
  rw [incl_wedgeOne, ← (TB g).totalRestrictRingHom_apply, map_mul,
    (TB g).totalRestrictRingHom_apply, (TB g).totalRestrictRingHom_apply,
    (TB g).totalRestrict_incl, (TB g).totalRestrict_incl]
  rfl

/-- The restriction of `c • x` is the product of the restrictions of `c` and `x`. -/
theorem incl_map_smul {O O' : Y.Opens} (φ : op O ⟶ op O') (p : ℤ)
    (c : (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O))
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.obj (op O)) :
    (TB g).incl p (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.map φ (c • x)) =
      sm g O' (Y.presheaf.map φ c) *
        (TB g).incl p (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.map φ x) :=
  (congrArg ((TB g).incl p) (PresheafOfModules.map_smul _ _ _ _)).trans
    (sm_mul_incl (g := g) _ p _).symm

variable (g) in
/-- The logarithmic derivative `a⁻¹ da` of a unit `a` with inverse `ai`. -/
noncomputable def dl (O : Y.Opens) (a ai : Γ(Y, O)) : (TB g).Total (op O) :=
  sm g O ai * δ g O a

/-- For a unit `a`, `da = a · (a⁻¹ da)`. -/
theorem δ_eq_sm_mul_dl {O : Y.Opens} {a ai : Γ(Y, O)} (h : ai * a = 1) :
    δ g O a = sm g O a * dl g O a ai := by
  unfold dl
  rw [← mul_assoc, ← map_mul, mul_comm a ai, h, map_one, one_mul]

/-- `d(ab)/(ab) = da/a + db/b`. -/
theorem dl_mul {O : Y.Opens} {a ai b bi : Γ(Y, O)} (ha : ai * a = 1) (hb : bi * b = 1) :
    dl g O (a * b) (ai * bi) = dl g O a ai + dl g O b bi := by
  unfold dl
  rw [δ_mul, mul_add, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul,
    show ai * bi * a = bi by rw [mul_right_comm, ha, one_mul],
    show ai * bi * b = ai by rw [mul_assoc, hb, mul_one], add_comm]

/-- The logarithmic derivative of `1` is zero. -/
theorem dl_one {O : Y.Opens} : dl g O 1 1 = 0 := by
  unfold dl
  rw [δ_one, mul_zero]

/-- `d(a^N)/a^N = N da/a`. -/
theorem dl_pow {O : Y.Opens} {a ai : Γ(Y, O)} (ha : ai * a = 1) (N : ℕ) :
    dl g O (a ^ N) (ai ^ N) = N • dl g O a ai := by
  induction N with
  | zero => rw [pow_zero, pow_zero, dl_one, zero_smul]
  | succ k ih =>
    rw [pow_succ, pow_succ, dl_mul (by rw [← mul_pow, ha, one_pow]) ha, ih, succ_nsmul]

/-- The logarithmic derivative of a unit does not depend on the choice of its inverse. -/
theorem dl_congr {O : Y.Opens} {a ai ai' : Γ(Y, O)} (h : ai * a = 1) (h' : ai' * a = 1) :
    dl g O a ai = dl g O a ai' := by
  have : ai = ai' := by
    calc ai = ai * (ai' * a) := by rw [h', mul_one]
      _ = ai' * (ai * a) := by ring
      _ = ai' := by rw [h, mul_one]
  rw [this]

/-- **The logarithmic derivative of an `N`-th root.** If `g^N = u v β` with all four units and
`c = (N u)⁻¹`, then `dg - c du · g = g · N⁻¹ (dv/v + dβ/β)`. -/
theorem dlog_twist_identity {O : Y.Opens} (N : ℕ) {c u gg v β ui vi βi gi Ni : Γ(Y, O)}
    (hu : ui * u = 1) (hv : vi * v = 1) (hβ : βi * β = 1) (hg : gi * gg = 1)
    (hN : Ni * (N : Γ(Y, O)) = 1) (hc : c = Ni * ui) (hrel : gg ^ N = u * v * β) :
    δ g O gg - sm g O c * δ g O u * sm g O gg =
      sm g O gg * (sm g O Ni * (dl g O v vi + dl g O β βi)) := by
  have hinv : (ui * vi * βi) * (gg ^ N) = 1 := by
    rw [hrel]
    calc ui * vi * βi * (u * v * β) = (ui * u) * (vi * v) * (βi * β) := by ring
      _ = 1 := by rw [hu, hv, hβ, one_mul, one_mul]
  have h1 : (N : ℕ) • dl g O gg gi = dl g O u ui + dl g O v vi + dl g O β βi := by
    rw [← dl_pow hg N, dl_congr (by rw [← mul_pow, hg, one_pow]) hinv, hrel,
      dl_mul (by rw [mul_mul_mul_comm, hu, hv, one_mul]) hβ, dl_mul hu hv]
  have h2 : dl g O gg gi = sm g O Ni * (dl g O u ui + dl g O v vi + dl g O β βi) := by
    rw [← h1, nsmul_eq_mul, ← map_natCast (sm g O) N, ← mul_assoc, ← map_mul, hN, map_one, one_mul]
  rw [δ_eq_sm_mul_dl hg, h2, hc, map_mul]
  have hcomm : sm g O Ni * sm g O ui * δ g O u * sm g O gg =
      sm g O gg * (sm g O Ni * dl g O u ui) := by
    unfold dl
    calc sm g O Ni * sm g O ui * δ g O u * sm g O gg =
        sm g O (Ni * ui) * (sm g O gg * δ g O u) := by
          rw [map_mul, mul_assoc _ (δ g O u), ← sm_comm gg (δ g O u)]
      _ = sm g O (gg * (Ni * ui)) * δ g O u := by rw [← mul_assoc, ← map_mul, mul_comm (Ni * ui)]
      _ = sm g O gg * (sm g O Ni * (sm g O ui * δ g O u)) := by
          rw [map_mul, map_mul, mul_assoc, mul_assoc]
  rw [hcomm]
  noncomm_ring

/-- The logarithmic derivative of `∏ₖ aₖ^{bₖ}` is `∑ₖ bₖ daₖ/aₖ`. -/
theorem dl_prod_pow {O : Y.Opens} {ι : Type*} (S : Finset ι) (a sa : ι → Γ(Y, O))
    (hs : ∀ k, sa k * a k = 1) (b : ι → ℕ) :
    dl g O (∏ k ∈ S, a k ^ b k) (∏ k ∈ S, sa k ^ b k) = ∑ k ∈ S, b k • dl g O (a k) (sa k) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Finset.sum_empty, dl_one]
  | insert x S hx ih =>
    have hinv : ∀ T : Finset ι, (∏ k ∈ T, sa k ^ b k) * (∏ k ∈ T, a k ^ b k) = 1 := fun T => by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun k _ => by rw [← mul_pow, hs k, one_pow]
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx,
      dl_mul (by rw [← mul_pow, hs x, one_pow]) (hinv S), dl_pow (hs x), ih]

/-- The algebra of the residue computation. -/
theorem residue_identity {O : Y.Opens} (N b : ℕ) {gg Hh t s v vi c u Ni : Γ(Y, O)}
    (hts : s * t = 1) (hNi : Ni * (N : Γ(Y, O)) = 1)
    (key : δ g O gg - sm g O c * δ g O u * sm g O gg =
      sm g O gg * (sm g O Ni * (dl g O v vi + b • dl g O t s))) :
    sm g O t * (N • (δ g O (gg * Hh) - sm g O c * δ g O u * sm g O (gg * Hh))) -
        b • (sm g O (gg * Hh) * δ g O t) =
      sm g O t * (sm g O (gg * N) * δ g O Hh + sm g O (gg * (Hh * vi)) * δ g O v) := by
  set θ := sm g O c * δ g O u
  have h1 : δ g O (gg * Hh) - θ * sm g O (gg * Hh) =
      sm g O Hh * (δ g O gg - θ * sm g O gg) + sm g O gg * δ g O Hh := by
    have hc : θ * sm g O gg * sm g O Hh = sm g O Hh * (θ * sm g O gg) := (sm_comm Hh _).symm
    rw [δ_mul, map_mul]
    calc sm g O gg * δ g O Hh + sm g O Hh * δ g O gg - θ * (sm g O gg * sm g O Hh) =
        sm g O gg * δ g O Hh + sm g O Hh * δ g O gg - θ * sm g O gg * sm g O Hh := by noncomm_ring
      _ = _ := by rw [hc]; noncomm_ring
  have hst : sm g O t * (sm g O s * δ g O t) = δ g O t := by
    rw [← mul_assoc, ← map_mul, mul_comm, hts, map_one, one_mul]
  rw [h1, key]
  unfold dl
  simp only [nsmul_eq_mul, ← map_natCast (sm g O)]
  simp only [mul_add, ← mul_assoc, ← map_mul]
  have e1 : t * (N : Γ(Y, O)) * Hh * gg * Ni * vi = t * gg * Hh * vi := by
    linear_combination (t * Hh * gg * vi) * hNi
  have e2 : t * (N : Γ(Y, O)) * Hh * gg * Ni * (b : Γ(Y, O)) * s = (b : Γ(Y, O)) * gg * Hh := by
    linear_combination ((b : Γ(Y, O)) * gg * Hh * s * t) * hNi + ((b : Γ(Y, O)) * gg * Hh) * hts
  have e3 : t * (N : Γ(Y, O)) * gg = t * gg * N := by ring
  rw [e1, e2, e3]
  abel

/-- The differential of a function `a`, as an element of degree zero, is `da`. -/
theorem Δ_zero_sm {O : Y.Opens} (a : Γ(Y, O)) : Δ g O 0 (sm g O a) = δ g O a := by
  have e : sm g O a = mon g O a [] := by simp [mon]
  rw [e, Δ_mon]
  simp [dmon]

end Twisted

/-- A function on an open, read as a scalar of the sheaves of modules on `Y`. -/
abbrev asStr {Y : Scheme.{u}} {O : Y.Opens} (a : Γ(Y, O)) :
    (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O) := a

/-- A section of the de Rham complex, read as a section of the sheaf of forms. -/
abbrev asPiece {Y S : Scheme.{u}} {g : Y ⟶ S} {O : Y.Opens} {p : ℕ}
    (x : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op O)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece (p : ℤ)).val.obj (op O) := x

section LogForms

open TopologicalSpace

namespace G1

variable {X S : Scheme.{u}}

/-- The graded algebra of forms on `U = X ∖ D`. -/
noncomputable abbrev TB (g : X ⟶ S) :=
  (Scheme.Hom.relativeDifferentialFormsAlgebra g).toPresheafGradedAlgebra

/-- The complement of the support of `D`. -/
abbrev LU (D : MMP.Mori.Divisor X) : X.Opens := D.supp.compl

/-- The form `d a` of a function `a` on an open of `X ∖ D`, as an element of degree one. -/
noncomputable def dOne (f : X ⟶ S) (D : MMP.Mori.Divisor X) (V : (LU D).toScheme.Opens)
    (a : Γ((LU D).toScheme, V)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece 1).val.obj (op V) :=
  (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials ((LU D).ι ≫ f))).val.app
    (op V) ((Scheme.Hom.universalRelativeDerivation ((LU D).ι ≫ f)).d (X := op V) a)

/-- The local generators of the logarithmic subring over an affine open `W'`. -/
noncomputable def gens (f : X ⟶ S) (D : MMP.Mori.Divisor X) (W' : X.affineOpens) :
    Set ((TB ((LU D).ι ≫ f)).Total (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens)))) :=
  Set.range (fun g : Γ(X, W') => (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom g)) ∪
    Set.range (fun g : Γ(X, W') =>
      (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ (((LU D).ι.app W').hom g))) ∪
    { η | ∃ E ∈ D.support, ∃ t : Γ(X, W'), E.idealSheaf.ideal W' = Ideal.span {t} ∧
      ∃ s : Γ((LU D).toScheme, (LU D).ι ⁻¹ᵁ (W' : X.Opens)), s * ((LU D).ι.app W').hom t = 1 ∧
        η = (TB ((LU D).ι ≫ f)).structureMap _ s *
          (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ (((LU D).ι.app W').hom t)) }

/-- The condition defining a logarithmic form on an affine open `W'`. -/
def Br (f : X ⟶ S) (D : MMP.Mori.Divisor X) (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.obj
      (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens)))) : Prop :=
  (TB ((LU D).ι ≫ f)).incl p ω ∈ AddSubgroup.closure { η | ∃ g ∈ I.ideal W',
    ∃ ζ ∈ Subring.closure (gens f D W'),
      η = (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom g) * ζ }

/-- Pulling functions back to an open `U` commutes with restriction. -/
theorem app_restrict {U : X.Opens} {W W' : X.Opens} (h : W' ≤ W) (g : Γ(X, W)) :
    U.toScheme.presheaf.map ((Opens.map U.ι.base).map (homOfLE h)).op ((U.ι.app W).hom g) =
      (U.ι.app W').hom (X.presheaf.map (homOfLE h).op g) := by
  have := congrArg (fun φ => φ.hom g) (U.ι.naturality (homOfLE h).op)
  exact this.symm

section Restrict

variable (f : X ⟶ S) (D : MMP.Mori.Divisor X)

/-- The structure map commutes with restriction. -/
theorem totalRestrict_structureMap {O O' : (LU D).toScheme.Opens} (φ : op O ⟶ op O')
    (c : Γ((LU D).toScheme, O)) :
    (TB ((LU D).ι ≫ f)).totalRestrict φ ((TB ((LU D).ι ≫ f)).structureMap _ c) =
      (TB ((LU D).ι ≫ f)).structureMap _ ((LU D).toScheme.presheaf.map φ c) :=
  (TB ((LU D).ι ≫ f)).structureMap_naturality _ c

/-- `dOne` commutes with restriction. -/
theorem totalRestrict_incl_dOne {O O' : (LU D).toScheme.Opens} (φ : op O ⟶ op O')
    (a : Γ((LU D).toScheme, O)) :
    (TB ((LU D).ι ≫ f)).totalRestrict φ ((TB ((LU D).ι ≫ f)).incl 1 (dOne f D O a)) =
      (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O' ((LU D).toScheme.presheaf.map φ a)) :=
  ((TB ((LU D).ι ≫ f)).totalRestrict_incl _ 1 _).trans (congrArg ((TB ((LU D).ι ≫ f)).incl 1)
    ((PresheafOfModules.naturality_apply
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials ((LU D).ι ≫ f))).val φ
        _).symm.trans (congrArg _
      ((Scheme.Hom.universalRelativeDerivation ((LU D).ι ≫ f)).d_map φ a).symm)))

/-- Restriction to a smaller affine open maps `gens` into `gens`. -/
theorem totalRestrict_mem_gens {W' W'' : X.affineOpens} (h : (W'' : X.Opens) ≤ W')
    {z} (hz : z ∈ gens f D W') :
    (TB ((LU D).ι ≫ f)).totalRestrict ((Opens.map (LU D).ι.base).map (homOfLE h)).op z ∈
      gens f D W'' := by
  rcases hz with (⟨g, rfl⟩ | ⟨g, rfl⟩) | ⟨E, hE, t, ht, s, hs, rfl⟩
  · refine Or.inl (Or.inl ⟨X.presheaf.map (homOfLE h).op g, ?_⟩)
    exact ((totalRestrict_structureMap f D _ _).trans
      (congrArg _ (app_restrict h g))).symm
  · refine Or.inl (Or.inr ⟨X.presheaf.map (homOfLE h).op g, ?_⟩)
    exact ((totalRestrict_incl_dOne f D _ _).trans
      (congrArg (fun a => (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ a)) (app_restrict h g))).symm
  · refine Or.inr ⟨E, hE, X.presheaf.map (homOfLE h).op t, ?_,
      (LU D).toScheme.presheaf.map ((Opens.map (LU D).ι.base).map (homOfLE h)).op s, ?_, ?_⟩
    · rw [← E.idealSheaf.map_ideal h, ht, Ideal.map_span, Set.image_singleton]
      rfl
    · rw [← app_restrict h t, ← map_mul, hs, map_one]
    · refine ((TB ((LU D).ι ≫ f)).totalRestrict_mul _ _ _).trans ?_
      refine congrArg₂ (· * ·) (totalRestrict_structureMap f D _ _) ?_
      exact (totalRestrict_incl_dOne f D _ _).trans
        (congrArg (fun a => (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ a)) (app_restrict h t))

/-- The condition `Br` is preserved by restriction to a smaller affine open. -/
theorem Br_restrict (I : X.IdealSheafData) (p : ℤ) {W' W'' : X.affineOpens}
    (h : (W'' : X.Opens) ≤ W') {ω} (hω : Br f D I p W' ω) :
    Br f D I p W'' (((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.map
      ((Opens.map (LU D).ι.base).map (homOfLE h)).op ω) := by
  let φ := ((Opens.map (LU D).ι.base).map (homOfLE h)).op
  let R := (TB ((LU D).ι ≫ f)).totalRestrictRingHom φ
  have hR : ∀ z, R z = (TB ((LU D).ι ≫ f)).totalRestrict φ z := fun z =>
    (TB ((LU D).ι ≫ f)).totalRestrictRingHom_apply φ z
  have hgens : Subring.closure (gens f D W') ≤ (Subring.closure (gens f D W'')).comap R :=
    Subring.closure_le.mpr fun z hz => by
      change R z ∈ Subring.closure (gens f D W'')
      rw [hR]
      exact Subring.subset_closure (totalRestrict_mem_gens f D h hz)
  have e : (TB ((LU D).ι ≫ f)).incl p
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.map φ ω) =
      R ((TB ((LU D).ι ≫ f)).incl p ω) :=
    ((hR _).trans ((TB ((LU D).ι ≫ f)).totalRestrict_incl φ p ω)).symm
  unfold Br
  rw [e]
  have hcl : AddSubgroup.closure { η | ∃ g ∈ I.ideal W',
      ∃ ζ ∈ Subring.closure (gens f D W'),
        η = (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom g) * ζ } ≤
      (AddSubgroup.closure { η | ∃ g ∈ I.ideal W'',
        ∃ ζ ∈ Subring.closure (gens f D W''),
          η = (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W'').hom g) * ζ }).comap
        R.toAddMonoidHom := by
    refine AddSubgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨g, hg, ζ, hζ, rfl⟩
    refine AddSubgroup.subset_closure ⟨X.presheaf.map (homOfLE h).op g,
      I.ideal_le_comap_ideal h hg, R ζ, hgens hζ, ?_⟩
    change R _ = _
    refine (map_mul R _ _).trans (congrArg (· * R ζ) ((hR _).trans
      ((totalRestrict_structureMap f D φ _).trans (congrArg _ (app_restrict h g)))))
  exact hcl hω

/-- The closure set defining `Br`. -/
noncomputable def BrSet (I : X.IdealSheafData) (W' : X.affineOpens) :
    AddSubgroup ((TB ((LU D).ι ≫ f)).Total (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens)))) :=
  AddSubgroup.closure { η | ∃ g ∈ I.ideal W', ∃ ζ ∈ Subring.closure (gens f D W'),
    η = (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom g) * ζ }

/-- `Br` is membership in `BrSet`. -/
theorem Br_iff (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens) (ω) :
    Br f D I p W' ω ↔ (TB ((LU D).ι ≫ f)).incl p ω ∈ BrSet f D I W' := Iff.rfl

/-- Zero satisfies `Br`. -/
theorem Br_zero (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens) : Br f D I p W' 0 := by
  rw [Br_iff, (TB ((LU D).ι ≫ f)).incl_zero]
  exact zero_mem _

/-- `Br` is closed under addition. -/
theorem Br_add (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens) {ω ω'}
    (h : Br f D I p W' ω) (h' : Br f D I p W' ω') : Br f D I p W' (ω + ω') := by
  rw [Br_iff, (TB ((LU D).ι ≫ f)).incl_add]
  exact add_mem h h'

/-- `BrSet` is closed under multiplication by functions on `W'`. -/
theorem structureMap_mul_mem_BrSet (I : X.IdealSheafData) (W' : X.affineOpens) (c : Γ(X, W'))
    {z} (hz : z ∈ BrSet f D I W') :
    (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom c) * z ∈ BrSet f D I W' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨g, hg, ζ, hζ, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨c * g, I.ideal W' |>.mul_mem_left c hg, ζ, hζ, ?_⟩
    rw [map_mul ((LU D).ι.app W').hom c g, ← mul_assoc]
    congr 1
    exact (map_mul ((TB ((LU D).ι ≫ f)).structureMap _) _ _).symm
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

/-- `incl (c • x)` is the image of `c` under the structure map times `incl x`. -/
theorem incl_smul_eq (p : ℤ) {O : (LU D).toScheme.Opens}
    (c : (Stacks.RingedSpace.structureRingSheaf (LU D).toScheme.toRingedSpace).obj.obj (op O))
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.obj (op O)) :
    (TB ((LU D).ι ≫ f)).incl p (c • x) =
      (TB ((LU D).ι ≫ f)).structureMap _ c * (TB ((LU D).ι ≫ f)).incl p x := by
  refine ((TB ((LU D).ι ≫ f)).incl_smul p c x).trans ?_
  change _ = c • (1 : (TB ((LU D).ι ≫ f)).Total (op O)) * _
  rw [(TB ((LU D).ι ≫ f)).smul_mul_eq, one_mul]

/-- `Br` is closed under multiplication by functions on `W'`. -/
theorem Br_smul (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens) (c : Γ(X, W')) {ω}
    (h : Br f D I p W' ω) :
    Br f D I p W' ((show (Stacks.RingedSpace.structureRingSheaf
      (LU D).toScheme.toRingedSpace).obj.obj (op _) from ((LU D).ι.app W').hom c) • ω) := by
  rw [Br_iff, incl_smul_eq]
  exact structureMap_mul_mem_BrSet f D I W' c h

/-- The restriction maps of the sheaf of forms on `X ∖ D`, indexed by opens of `X`. -/
noncomputable abbrev rs (p : ℤ) {W W' : X.Opens} (h : W' ≤ W)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.obj
        (op ((LU D).ι ⁻¹ᵁ W))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.obj
      (op ((LU D).ι ⁻¹ᵁ W')) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.map
    ((Opens.map (LU D).ι.base).map (homOfLE h)).op ω

/-- Restriction `rs` is transitive. -/
theorem rs_rs (p : ℤ) {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (ω) :
    rs f D p h' (rs f D p h ω) = rs f D p (h'.trans h) ω :=
  (PresheafOfModules.map_comp_apply _ ((Opens.map (LU D).ι.base).map (homOfLE h)).op
    ((Opens.map (LU D).ι.base).map (homOfLE h')).op ω).symm.trans
    (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) ω)

end Restrict

section RLF

variable (n : ℕ) (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X)
  (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData) (p : ℤ)

/-- A form is logarithmic if and only if near every point it satisfies `Br` on an affine open. -/
theorem mem_relativeLogForms_iff' (W : X.Opens) (ω) :
    ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W ↔
      ∀ x ∈ W, ∃ (W' : X.affineOpens) (h : (W' : X.Opens) ≤ W), x ∈ (W' : X.Opens) ∧
        Br f D I p W' (rs f D p h ω) := Iff.rfl

/-- Every point of an open `W` has an affine open neighbourhood contained in `W`. -/
theorem exists_affineOpens_le {W : X.Opens} {x : X} (hx : x ∈ W) :
    ∃ W' : X.affineOpens, x ∈ (W' : X.Opens) ∧ (W' : X.Opens) ≤ W := by
  obtain ⟨W', hW', hx', h⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨⟨W', hW'⟩, hx', h⟩

/-- Logarithmic forms restrict to logarithmic forms. -/
theorem relativeLogForms_restrict {W V : X.Opens} (h : V ≤ W) {ω}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W) :
    rs f D p h ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p V := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨W', hW', hxW', hb⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω x (h hx)
  obtain ⟨W'', hxW'', hle⟩ := exists_affineOpens_le (X := X) (show x ∈ (W' : X.Opens) ⊓ V from
    ⟨hxW', hx⟩)
  refine ⟨W'', hle.trans inf_le_right, hxW'', ?_⟩
  have e : rs f D p (hle.trans inf_le_right) (rs f D p h ω) =
      rs f D p (hle.trans inf_le_left) (rs f D p hW' ω) := by
    rw [rs_rs, rs_rs]
  rw [e]
  exact Br_restrict f D I p (hle.trans inf_le_left) hb

/-- A form which is logarithmic near every point is logarithmic. -/
theorem relativeLogForms_of_local {W : X.Opens} {ω}
    (H : ∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧
      rs f D p h ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p V) :
    ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨V, hV, hxV, hω⟩ := H x hx
  obtain ⟨W', hW', hxW', hb⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω x hxV
  refine ⟨W', hW'.trans hV, hxW', ?_⟩
  rw [← rs_rs f D p hV hW']
  exact hb

/-- Zero is a logarithmic form. -/
theorem zero_mem_relativeLogForms (W : X.Opens) :
    0 ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨W', hxW', hle⟩ := exists_affineOpens_le (X := X) hx
  refine ⟨W', hle, hxW', ?_⟩
  rw [show rs f D p hle 0 = 0 from map_zero _]
  exact Br_zero f D I p W'

/-- Logarithmic forms are closed under addition. -/
theorem add_mem_relativeLogForms {W : X.Opens} {ω ω'}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W)
    (hω' : ω' ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W) :
    ω + ω' ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨W₁, h₁, hx₁, hb₁⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω x hx
  obtain ⟨W₂, h₂, hx₂, hb₂⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω' x hx
  obtain ⟨W'', hxW'', hle⟩ := exists_affineOpens_le (X := X)
    (show x ∈ (W₁ : X.Opens) ⊓ W₂ from ⟨hx₁, hx₂⟩)
  refine ⟨W'', hle.trans (inf_le_left.trans h₁), hxW'', ?_⟩
  rw [show rs f D p (hle.trans (inf_le_left.trans h₁)) (ω + ω') =
      rs f D p (hle.trans (inf_le_left.trans h₁)) ω +
        rs f D p (hle.trans (inf_le_left.trans h₁)) ω' from map_add _ _ _]
  refine Br_add f D I p W'' ?_ ?_
  · rw [← rs_rs f D p h₁ (hle.trans inf_le_left)]
    exact Br_restrict f D I p _ hb₁
  · rw [show hle.trans (inf_le_left.trans h₁) = (hle.trans inf_le_right).trans h₂ from rfl,
      ← rs_rs f D p h₂ (hle.trans inf_le_right)]
    exact Br_restrict f D I p _ hb₂

/-- Logarithmic forms are closed under multiplication by functions on `W`. -/
theorem smul_mem_relativeLogForms {W : X.Opens} (c : Γ(X, W)) {ω}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W) :
    (show (Stacks.RingedSpace.structureRingSheaf
      (LU D).toScheme.toRingedSpace).obj.obj (op _) from ((LU D).ι.app W).hom c) • ω ∈
      MMP.Mori.Divisor.relativeLogForms n f D hD I p W := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨W', hW', hxW', hb⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω x hx
  refine ⟨W', hW', hxW', ?_⟩
  have e : rs f D p hW' ((show (Stacks.RingedSpace.structureRingSheaf
      (LU D).toScheme.toRingedSpace).obj.obj (op _) from ((LU D).ι.app W).hom c) • ω) =
      (show (Stacks.RingedSpace.structureRingSheaf
      (LU D).toScheme.toRingedSpace).obj.obj (op _) from ((LU D).ι.app W').hom
        (X.presheaf.map (homOfLE hW').op c)) • rs f D p hW' ω := by
    refine (PresheafOfModules.map_smul _ _ _ _).trans ?_
    exact congrArg (· • rs f D p hW' ω) (app_restrict hW' c)
  rw [e]
  exact Br_smul f D I p W' _ hb

end RLF

section Complex

variable (f : X ⟶ S) (U : X.Opens)

/-- The comparison `f⁻¹𝒪_S ⟶ j_*((j ≫ f)⁻¹𝒪_S)` (the transpose of the unit of
`(j ≫ f)⁻¹ ⊣ (j ≫ f)_*`), followed by `j_*` of the structure map of `j ≫ f`, is the structure map
of `f` followed by `𝒪_X ⟶ j_*𝒪_U`, for `j = U.ι`. -/
theorem phi_comp_str {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).symm
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (U.ι ≫ f).base).unit.app
        S.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} U.ι.base).map (inverseImageStructureMap (U.ι ≫ f)) =
    inverseImageStructureMap f ≫
      (⟨U.ι.c⟩ : X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} U.ι.base).obj
          U.toScheme.sheaf) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply]
  erw [Adjunction.homEquiv_naturality_right]
  have h1 : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (U.ι ≫ f).base).unit.app
      S.sheaf ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} (U.ι ≫ f).base).map
        (inverseImageStructureMap (U.ι ≫ f)) = ⟨(U.ι ≫ f).c⟩ :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (U.ι ≫ f).base).homEquiv_unit
      _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have h2 : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _)
      (inverseImageStructureMap f) = ⟨f.c⟩ := Equiv.apply_symm_apply _ _
  erw [h2]
  exact h1.trans rfl

/-- The comparison `f⁻¹𝒪_S ⟶ j_*((j ≫ f)⁻¹𝒪_S)` of the definition of the logarithmic complex. -/
noncomputable def phiS :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} U.ι.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} (U.ι ≫ f).base).obj S.sheaf) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).symm
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (U.ι ≫ f).base).unit.app
      S.sheaf)

/-- `phiS` is compatible with the structure maps of `f` and of `U.ι ≫ f`. -/
theorem phiS_apply {W : X.Opens}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.obj (op W)) :
    ((inverseImageStructureMap (U.ι ≫ f)).hom.app (op (U.ι ⁻¹ᵁ W))).hom
        (((phiS f U).hom.app (op W)).hom a) =
      (U.ι.app W).hom (((inverseImageStructureMap f).hom.app (op W)).hom a) :=
  congrArg (fun φ => (φ.hom.app (op W)).hom a) (phi_comp_str f U)

/-- The direct image `j_*` over the base rings, as in the definition of the logarithmic
complex. -/
noncomputable abbrev jStar : SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} (U.ι ≫ f).base).obj S.sheaf)) ⥤
    SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) :=
  let φ : (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} U.ι.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} (U.ι ≫ f).base).obj S.sheaf) := phiS f U
  SheafOfModules.pushforward.{u} (F := Opens.map U.ι.base)
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map φ)

/-- The term `j_*Ω^p_{U/S}`. -/
noncomputable abbrev KX (p : ℕ) : SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) :=
  (jStar f U).obj ((Scheme.Hom.deRhamComplex (U.ι ≫ f)).X p)

/-- The action of `f⁻¹𝒪_S` on `j_*Ω^p_{U/S}` is through the functions on `U`. -/
theorem KX_smul (p : ℕ) {W : X.Opens}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.obj (op W))
    (ω : (KX f U p).val.obj (op W)) :
    a • ω = (show (Stacks.RingedSpace.structureRingSheaf U.toScheme.toRingedSpace).obj.obj
      (op (U.ι ⁻¹ᵁ W)) from (U.ι.app W).hom (((inverseImageStructureMap f).hom.app (op W)).hom a)) •
        (show ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ f)).piece p).val.obj
          (op (U.ι ⁻¹ᵁ W)) from ω) := by
  rw [← phiS_apply f U a]
  rfl

end Complex

end G1

end LogForms

namespace B1

/-! ### Logarithmic forms on the complement of a divisor -/

section Log

variable {X S : Scheme.{u}} (f : X ⟶ S) (D : MMP.Mori.Divisor X)

/-- The complement `U = X ∖ D` of the support of a divisor. -/
abbrev Uc : X.Opens := D.supp.compl

/-- The morphism `U ⟶ S`. -/
abbrev gU : (Uc D).toScheme ⟶ S := (Uc D).ι ≫ f

/-- Restriction of functions from an open of `X` to its trace on `U`. -/
abbrev res (W' : X.Opens) : Γ(X, W') →+* Γ((Uc D).toScheme, (Uc D).ι ⁻¹ᵁ W') :=
  ((Uc D).ι.app W').hom

/-- The generators of the logarithmic forms over an affine open `W'`: functions, their
differentials, and the forms `dt/t` for local equations `t` of components of `D`. -/
def gens (W' : X.affineOpens) :
    Set ((TB (gU f D)).Total (op ((Uc D).ι ⁻¹ᵁ (W' : X.Opens)))) :=
  Set.range (fun a => sm (gU f D) _ (res D W' a)) ∪
    Set.range (fun a => δ (gU f D) _ (res D W' a)) ∪
    {η | ∃ E ∈ D.support, ∃ t : Γ(X, W'), E.idealSheaf.ideal W' = Ideal.span {t} ∧
      ∃ s, s * res D W' t = 1 ∧ η = sm (gU f D) _ s * δ (gU f D) _ (res D W' t)}

/-- The `I`-multiples of the ring generated by `gens`. -/
noncomputable def logClosure (I : X.IdealSheafData) (W' : X.affineOpens) :
    AddSubgroup ((TB (gU f D)).Total (op ((Uc D).ι ⁻¹ᵁ (W' : X.Opens)))) :=
  AddSubgroup.closure {η | ∃ a ∈ I.ideal W', ∃ ζ ∈ Subring.closure (gens f D W'),
    η = sm (gU f D) _ (res D W' a) * ζ}

/-- A form on `U ∩ W` lies in `I · Ω^p_{X/S}(log D)` if and only if near every point its
restriction to some affine open `W'` lies in `logClosure f D I W'`. -/
theorem mem_relativeLogForms_iff (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData) (p : ℤ) (W : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece p).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W))) :
    ω ∈ relativeLogForms n f D hD I p W ↔
      ∀ x ∈ W, ∃ (W' : X.affineOpens) (h : (W' : X.Opens) ≤ W), x ∈ (W' : X.Opens) ∧
        (TB (gU f D)).incl p (((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece
          p).val.map ((Opens.map (Uc D).ι.base).map (homOfLE h)).op ω) ∈
          logClosure f D I W' :=
  Iff.rfl

/-- `res` commutes with restriction. -/
theorem res_restrict {W₁ W' : X.Opens} (h : W₁ ≤ W') (a : Γ(X, W')) :
    (Uc D).toScheme.presheaf.map ((Opens.map (Uc D).ι.base).map (homOfLE h)).op (res D W' a) =
      res D W₁ (X.presheaf.map (homOfLE h).op a) :=
  (ConcreteCategory.congr_hom ((Uc D).ι.naturality (homOfLE h).op) a).symm

/-- Restriction to a smaller affine open maps `gens` into `gens`. -/
theorem gens_restrict {W₁ W' : X.affineOpens} (h : (W₁ : X.Opens) ≤ W')
    {z : (TB (gU f D)).Total (op ((Uc D).ι ⁻¹ᵁ (W' : X.Opens)))} (hz : z ∈ gens f D W') :
    (TB (gU f D)).totalRestrict ((Opens.map (Uc D).ι.base).map (homOfLE h)).op z ∈
      gens f D W₁ := by
  rcases hz with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨E, hE, t, ht, s, hs, rfl⟩
  · refine Or.inl (Or.inl ⟨X.presheaf.map (homOfLE h).op a, ?_⟩)
    rw [totalRestrict_sm, res_restrict]
  · refine Or.inl (Or.inr ⟨X.presheaf.map (homOfLE h).op a, ?_⟩)
    rw [totalRestrict_δ, res_restrict]
  · refine Or.inr ⟨E, hE, X.presheaf.map (homOfLE h).op t, ?_,
      (Uc D).toScheme.presheaf.map ((Opens.map (Uc D).ι.base).map (homOfLE h)).op s, ?_, ?_⟩
    · rw [← E.idealSheaf.map_ideal h, ht, Ideal.map_span, Set.image_singleton]
      rfl
    · rw [← res_restrict, ← map_mul, hs, map_one]
    · rw [Stacks.GradedAlgebra.totalRestrict_mul, totalRestrict_sm, totalRestrict_δ,
        res_restrict]

/-- Restriction to a smaller affine open maps the ring generated by `gens` into the ring generated
by `gens`. -/
theorem closure_gens_restrict {W₁ W' : X.affineOpens} (h : (W₁ : X.Opens) ≤ W')
    {z : (TB (gU f D)).Total (op ((Uc D).ι ⁻¹ᵁ (W' : X.Opens)))}
    (hz : z ∈ Subring.closure (gens f D W')) :
    (TB (gU f D)).totalRestrict ((Opens.map (Uc D).ι.base).map (homOfLE h)).op z ∈
      Subring.closure (gens f D W₁) := by
  let ρ := (TB (gU f D)).totalRestrictRingHom ((Opens.map (Uc D).ι.base).map (homOfLE h)).op
  have : Subring.closure (gens f D W') ≤ (Subring.closure (gens f D W₁)).comap ρ :=
    Subring.closure_le.mpr fun z hz => Subring.subset_closure (gens_restrict f D h hz)
  exact this hz

/-- Restriction to a smaller affine open maps `logClosure f D I` into `logClosure f D I`. -/
theorem logClosure_restrict (I : X.IdealSheafData) {W₁ W' : X.affineOpens}
    (h : (W₁ : X.Opens) ≤ W')
    {z : (TB (gU f D)).Total (op ((Uc D).ι ⁻¹ᵁ (W' : X.Opens)))} (hz : z ∈ logClosure f D I W') :
    (TB (gU f D)).totalRestrict ((Opens.map (Uc D).ι.base).map (homOfLE h)).op z ∈
      logClosure f D I W₁ := by
  let ρ := (TB (gU f D)).totalRestrictRingHom ((Opens.map (Uc D).ι.base).map (homOfLE h)).op
  have : logClosure f D I W' ≤ (logClosure f D I W₁).comap ρ.toAddMonoidHom := by
    refine AddSubgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨a, ha, ζ, hζ, rfl⟩
    refine AddSubgroup.subset_closure ⟨X.presheaf.map (homOfLE h).op a,
      I.ideal_le_comap_ideal h ha, _, closure_gens_restrict f D h hζ, ?_⟩
    change (TB (gU f D)).totalRestrict _ (_ * _) = _
    rw [Stacks.GradedAlgebra.totalRestrict_mul, totalRestrict_sm, res_restrict]
  exact this hz

/-- Every element of `gens` is a product `b · dc₁ ∧ ⋯ ∧ dc_p` whose differential lies in the ring
generated by `gens`. -/
theorem gens_hG (W' : X.affineOpens) :
    ∀ z ∈ gens f D W', ∃ b l, z = mon (gU f D) _ b l ∧
      dmon (gU f D) _ b l ∈ Subring.closure (gens f D W') := by
  rintro _ ((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨E, hE, t, ht, s, hs, rfl⟩)
  · refine ⟨res D W' a, [], by simp [mon], ?_⟩
    simp only [dmon, List.map_nil, List.prod_nil, mul_one]
    exact Subring.subset_closure (Or.inl (Or.inr ⟨a, rfl⟩))
  · refine ⟨1, [res D W' a], by simp [mon], ?_⟩
    simp only [dmon, δ_one, zero_mul]
    exact Subring.zero_mem _
  · refine ⟨s, [res D W' t], by simp [mon], ?_⟩
    simp only [dmon, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [δ_mul_δ_of_mul_eq_one hs]
    exact Subring.zero_mem _

/-- The differential maps the logarithmic forms over an affine open to themselves. -/
theorem Δ_mem_logClosure_top (W' : X.affineOpens) (p : ℕ)
    {z : (TB (gU f D)).Total (op ((Uc D).ι ⁻¹ᵁ (W' : X.Opens)))} (hz : z ∈ logClosure f D ⊤ W') :
    Δ (gU f D) _ p z ∈ logClosure f D ⊤ W' := by
  refine Δ_mem_closure (gens f D W') (gens_hG f D W') (res D W')
    ((⊤ : X.IdealSheafData).ideal W' : Set Γ(X, W')) ?_ p hz
  intro a _
  refine ⟨1, Submodule.mem_top, δ (gU f D) _ (res D W' a),
    Subring.subset_closure (Or.inl (Or.inr ⟨a, rfl⟩)), ?_⟩
  rw [map_one, map_one, one_mul]

/-- The de Rham differential commutes with restriction. -/
theorem deRham_restrict (p : ℕ) {W' W'' : X.Opens} (h : W' ≤ W'')
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece p).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W''))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece ((p + 1 : ℕ) : ℤ)).val.map
        ((Opens.map (Uc D).ι.base).map (homOfLE h)).op
        (((Scheme.Hom.deRhamComplex (gU f D)).d p (p + 1)).val.app (op ((Uc D).ι ⁻¹ᵁ W'')) ω) =
      ((Scheme.Hom.deRhamComplex (gU f D)).d p (p + 1)).val.app (op ((Uc D).ι ⁻¹ᵁ W'))
        (((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece p).val.map
          ((Opens.map (Uc D).ι.base).map (homOfLE h)).op ω) :=
  (PresheafOfModules.naturality_apply ((Scheme.Hom.deRhamComplex (gU f D)).d p (p + 1)).val
    ((Opens.map (Uc D).ι.base).map (homOfLE h)).op ω).symm

/-- **The differential preserves `Ω^•_{X/S}(log D)`.** -/
theorem deRham_mem_relativeLogForms_top (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) (p : ℕ) (W'' : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece p).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W'')))
    (hω : ω ∈ relativeLogForms n f D hD ⊤ p W'') :
    ((Scheme.Hom.deRhamComplex (gU f D)).d p (p + 1)).val.app (op ((Uc D).ι ⁻¹ᵁ W'')) ω ∈
      relativeLogForms n f D hD ⊤ ((p + 1 : ℕ) : ℤ) W'' := by
  rw [mem_relativeLogForms_iff] at hω
  refine (mem_relativeLogForms_iff f D n hD _ _ _ _).mpr fun x hx => ?_
  obtain ⟨W', h, hxW', hmem⟩ := hω x hx
  refine ⟨W', h, hxW', ?_⟩
  exact (congrArg (· ∈ logClosure f D ⊤ W')
    ((congrArg ((TB (gU f D)).incl ((p + 1 : ℕ) : ℤ)) (deRham_restrict f D p h ω)).trans
      (Δ_incl p _).symm)).mpr (Δ_mem_logClosure_top f D W' p hmem)

/-- A section over `O` is a unit as soon as it is invertible at every point of `O`. -/
theorem isUnit_of_le_basicOpen {Y : Scheme.{u}} {O : Y.Opens} (a : Γ(Y, O))
    (h : O ≤ Y.basicOpen a) : IsUnit a :=
  RingedSpace.isUnit_of_isUnit_germ Y.toRingedSpace O a fun x hx =>
    (Y.mem_basicOpen a x hx).mp (h hx)

/-- A local equation of a component of `D` is invertible on the complement `U` of `D`. -/
theorem isUnit_res_of_ideal_eq {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ D.support)
    {W₁ : X.affineOpens} {t : Γ(X, W₁)} (ht : E.idealSheaf.ideal W₁ = Ideal.span {t}) :
    IsUnit (res D W₁ t) := by
  refine isUnit_of_le_basicOpen _ fun y hy => ?_
  rw [← Scheme.preimage_basicOpen]
  by_contra hyt
  have hyW : ((Uc D).ι y) ∈ (W₁ : X.Opens) := hy
  have hmem : (Uc D).ι y ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support, SetLike.mem_coe,
      E.idealSheaf.mem_support_iff_of_mem hyW, ht, Scheme.mem_zeroLocus_iff]
    intro b hb hyb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    rw [Scheme.basicOpen_mul] at hyb
    exact hyt hyb.2
  exact (y.2 : (Uc D).ι y ∉ D.supp) (MMP.Mori.DivisorWithCoeffs.support_subset_supp
    (Finsupp.mem_support_iff.mp hE) hmem)

/-- Restricting twice in the total ring of forms is restricting once. -/
theorem totalRestrict_incl_map (p : ℤ) {W₁ W' W'' : X.Opens} (h₁ : W₁ ≤ W') (h : W' ≤ W'')
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece p).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W''))) :
    (TB (gU f D)).totalRestrict ((Opens.map (Uc D).ι.base).map (homOfLE h₁)).op
        ((TB (gU f D)).incl p (((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece
          p).val.map ((Opens.map (Uc D).ι.base).map (homOfLE h)).op ω)) =
      (TB (gU f D)).incl p (((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece
          p).val.map ((Opens.map (Uc D).ι.base).map (homOfLE (h₁.trans h))).op ω) :=
  ((TB (gU f D)).totalRestrict_incl _ p _).trans (congrArg ((TB (gU f D)).incl p)
    ((Stacks.sectionRestrict_comp _ _ _ ω).symm.trans
      (congrArg (fun φ => Stacks.sectionRestrict _ φ ω) (Subsingleton.elim _ _))))

/-- On an affine open where `I` is generated by a product `t₁ ⋯ t_r` of local equations of
components of `D`, the differential maps `I · Ω^•(log D)` to itself. -/
theorem Δ_mem_logClosure_of_ideal_eq (I : X.IdealSheafData) {W₁ : X.affineOpens} {r : ℕ}
    (j : Fin r → MMP.Mori.PrimeDivisor X) (t : Fin r → Γ(X, W₁))
    (hjD : ∀ i, j i ∈ D.support ∧ (j i).idealSheaf.ideal W₁ = Ideal.span {t i})
    (hIW : I.ideal W₁ = Ideal.span {∏ i, t i}) (p : ℕ)
    {z : (TB (gU f D)).Total (op ((Uc D).ι ⁻¹ᵁ (W₁ : X.Opens)))}
    (hz : z ∈ logClosure f D I W₁) :
    Δ (gU f D) _ p z ∈ logClosure f D I W₁ := by
  have hu : ∀ i, IsUnit (res D W₁ (t i)) := fun i =>
    isUnit_res_of_ideal_eq D (hjD i).1 (hjD i).2
  let s : Fin r → Γ((Uc D).toScheme, (Uc D).ι ⁻¹ᵁ (W₁ : X.Opens)) := fun i => ↑(hu i).unit⁻¹
  have hs : ∀ i, s i * res D W₁ (t i) = 1 := fun i => (hu i).val_inv_mul
  refine Δ_mem_closure (gens f D W₁) (gens_hG f D W₁) (res D W₁)
    (I.ideal W₁ : Set Γ(X, W₁)) ?_ p hz
  intro a ha
  rw [SetLike.mem_coe, hIW] at ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  refine ⟨∏ i, t i, by rw [SetLike.mem_coe, hIW]; exact Ideal.mem_span_singleton_self _,
    δ (gU f D) _ (res D W₁ b) + sm (gU f D) _ (res D W₁ b) *
      ∑ i, sm (gU f D) _ (s i) * δ (gU f D) _ (res D W₁ (t i)), ?_, ?_⟩
  · refine Subring.add_mem _ (Subring.subset_closure (Or.inl (Or.inr ⟨b, rfl⟩)))
      (Subring.mul_mem _ (Subring.subset_closure (Or.inl (Or.inl ⟨b, rfl⟩)))
        (Subring.sum_mem _ fun i _ => Subring.subset_closure
          (Or.inr ⟨j i, (hjD i).1, t i, (hjD i).2, s i, hs i, rfl⟩)))
  · rw [map_mul, map_prod, δ_mul, δ_prod_eq _ s hs, mul_add, add_comm]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm]

/-- **The differential preserves `I · Ω^•_{X/S}(log D)`** for an ideal `I` which is, locally,
generated by a product of local equations of components of `D`. -/
theorem deRham_mem_relativeLogForms_of_charts (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData)
    (hchart : ∀ x : X, ∃ (Wc : X.affineOpens) (r : ℕ) (j : Fin r → MMP.Mori.PrimeDivisor X)
      (t : Fin r → Γ(X, Wc)), x ∈ (Wc : X.Opens) ∧
        (∀ i, j i ∈ D.support ∧ (j i).idealSheaf.ideal Wc = Ideal.span {t i}) ∧
        I.ideal Wc = Ideal.span {∏ i, t i})
    (p : ℕ) (W'' : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece p).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W'')))
    (hω : ω ∈ relativeLogForms n f D hD I p W'') :
    ((Scheme.Hom.deRhamComplex (gU f D)).d p (p + 1)).val.app (op ((Uc D).ι ⁻¹ᵁ W'')) ω ∈
      relativeLogForms n f D hD I ((p + 1 : ℕ) : ℤ) W'' := by
  rw [mem_relativeLogForms_iff] at hω
  refine (mem_relativeLogForms_iff f D n hD _ _ _ _).mpr fun x hx => ?_
  obtain ⟨W', h, hxW', hmem⟩ := hω x hx
  obtain ⟨Wc, rc, jc, tc, hxc, hjDc, hIWc⟩ := hchart x
  obtain ⟨U₁, hU₁, hxU₁, hU₁le⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (W' : X.Opens) ⊓ Wc from ⟨hxW', hxc⟩)
  let W₁ : X.affineOpens := ⟨U₁, hU₁⟩
  have h₁ : (W₁ : X.Opens) ≤ W' := hU₁le.trans inf_le_left
  have h₁c : (W₁ : X.Opens) ≤ Wc := hU₁le.trans inf_le_right
  refine ⟨W₁, h₁.trans h, hxU₁, ?_⟩
  have hmem₁ := (congrArg (· ∈ logClosure f D I W₁)
    (totalRestrict_incl_map f D (p : ℤ) h₁ h ω)).mp (logClosure_restrict f D I h₁ hmem)
  have key := Δ_mem_logClosure_of_ideal_eq f D I (W₁ := W₁) jc
    (fun i => X.presheaf.map (homOfLE h₁c).op (tc i))
    (fun i => ⟨(hjDc i).1, by
      rw [← (jc i).idealSheaf.map_ideal h₁c, (hjDc i).2, Ideal.map_span, Set.image_singleton]
      rfl⟩)
    (by
      rw [← I.map_ideal h₁c, hIWc, Ideal.map_span, Set.image_singleton, map_prod]
      rfl) p hmem₁
  exact (congrArg (· ∈ logClosure f D I W₁)
    ((congrArg ((TB (gU f D)).incl ((p + 1 : ℕ) : ℤ)) (deRham_restrict f D p (h₁.trans h) ω)).trans
      (Δ_incl p _).symm)).mpr key

/-- **The differential preserves `Ω^•_{X/S}(log D)(-D)`.** -/
theorem deRham_mem_relativeLogForms_suppIdeal (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) (p : ℕ) (W'' : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece p).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W'')))
    (hω : ω ∈ relativeLogForms n f D hD D.suppIdeal p W'') :
    ((Scheme.Hom.deRhamComplex (gU f D)).d p (p + 1)).val.app (op ((Uc D).ι ⁻¹ᵁ W'')) ω ∈
      relativeLogForms n f D hD D.suppIdeal ((p + 1 : ℕ) : ℤ) W'' :=
  deRham_mem_relativeLogForms_of_charts f D n hD D.suppIdeal (fun x => by
    obtain ⟨Wc, -, -, tc, hxc, -, rc, hrc, jc, -, hjDc, hDWc⟩ := hD.2 x
    exact ⟨Wc, rc, jc, fun i => tc (Fin.castLE hrc i), hxc,
      fun i => ⟨(hjDc i).1, (hjDc i).2.2⟩, hDWc⟩) p W'' ω hω

/-- `logClosure f D ⊤ W'` is contained in the ring generated by `gens f D W'`. -/
theorem logClosure_top_le (W' : X.affineOpens) :
    logClosure f D ⊤ W' ≤ (Subring.closure (gens f D W')).toAddSubgroup := by
  refine AddSubgroup.closure_le _ |>.mpr ?_
  rintro _ ⟨a, -, ζ, hζ, rfl⟩
  exact Subring.mul_mem _ (Subring.subset_closure (Or.inl (Or.inl ⟨a, rfl⟩))) hζ

/-- Products of logarithmic forms with `I`-twisted logarithmic forms are `I`-twisted. -/
theorem mul_mem_logClosure (I : X.IdealSheafData) (W' : X.affineOpens)
    {z₁ z₂ : (TB (gU f D)).Total (op ((Uc D).ι ⁻¹ᵁ (W' : X.Opens)))}
    (h₁ : z₁ ∈ logClosure f D ⊤ W') (h₂ : z₂ ∈ logClosure f D I W') :
    z₁ * z₂ ∈ logClosure f D I W' := by
  have h₁' : z₁ ∈ Subring.closure (gens f D W') := logClosure_top_le f D W' h₁
  induction h₂ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, ζ, hζ, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, z₁ * ζ, Subring.mul_mem _ h₁' hζ, ?_⟩
    rw [← mul_assoc, ← mul_assoc, sm_comm (res D W' a) z₁]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

/-- The wedge of a logarithmic one-form with an `I`-twisted logarithmic form is `I`-twisted. -/
theorem wedgeOne_mem_relativeLogForms (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData) (p : ℕ) (W : X.Opens)
    (ξ : ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece 1).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W)))
    (η : ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece (p : ℤ)).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W)))
    (hξ : ξ ∈ relativeLogForms n f D hD ⊤ 1 W) (hη : η ∈ relativeLogForms n f D hD I p W) :
    wedgeOne (gU f D) p ξ η ∈ relativeLogForms n f D hD I ((p + 1 : ℕ) : ℤ) W := by
  refine (mem_relativeLogForms_iff f D n hD _ _ _ _).mpr fun x hx => ?_
  obtain ⟨W₁, h₁, hx₁, m₁⟩ := (mem_relativeLogForms_iff f D n hD _ _ _ _).mp hξ x hx
  obtain ⟨W₂, h₂, hx₂, m₂⟩ := (mem_relativeLogForms_iff f D n hD _ _ _ _).mp hη x hx
  obtain ⟨U₃, hU₃, hx₃, hle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (W₁ : X.Opens) ⊓ W₂ from ⟨hx₁, hx₂⟩)
  let W₃ : X.affineOpens := ⟨U₃, hU₃⟩
  have k₁ : (W₃ : X.Opens) ≤ W₁ := hle.trans inf_le_left
  have k₂ : (W₃ : X.Opens) ≤ W₂ := hle.trans inf_le_right
  refine ⟨W₃, k₁.trans h₁, hx₃, ?_⟩
  have m₁' := (congrArg (· ∈ logClosure f D ⊤ W₃) (totalRestrict_incl_map f D 1 k₁ h₁ ξ)).mp
    (logClosure_restrict f D ⊤ k₁ m₁)
  have m₂' := (congrArg (· ∈ logClosure f D I W₃) (totalRestrict_incl_map f D (p : ℤ) k₂ h₂ η)).mp
    (logClosure_restrict f D I k₂ m₂)
  set φ := ((Opens.map (Uc D).ι.base).map (homOfLE (k₁.trans h₁))).op
  have e : (TB (gU f D)).incl ((p + 1 : ℕ) : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece ((p + 1 : ℕ) : ℤ)).val.map φ
        (wedgeOne (gU f D) p ξ η)) =
      (TB (gU f D)).incl 1 (((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece 1).val.map
        φ ξ) * (TB (gU f D)).incl (p : ℤ)
          (((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece (p : ℤ)).val.map φ η) := by
    refine ((TB (gU f D)).totalRestrict_incl φ _ _).symm.trans ?_
    rw [incl_wedgeOne, ← (TB (gU f D)).totalRestrictRingHom_apply, map_mul,
      (TB (gU f D)).totalRestrictRingHom_apply, (TB (gU f D)).totalRestrictRingHom_apply,
      (TB (gU f D)).totalRestrict_incl, (TB (gU f D)).totalRestrict_incl]
    rfl
  exact e ▸ mul_mem_logClosure f D I W₃ m₁' m₂'

/-- The differential of a function is a logarithmic one-form. -/
theorem δ_mem_relativeLogForms (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) (W : X.Opens) (a : Γ(X, W)) :
    (show ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece 1).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W)) from
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials (gU f D))).val.app
        (op ((Uc D).ι ⁻¹ᵁ W)) ((Scheme.Hom.universalRelativeDerivation (gU f D)).d
          (X := op ((Uc D).ι ⁻¹ᵁ W)) (res D W a))) ∈ relativeLogForms n f D hD ⊤ 1 W := by
  refine (mem_relativeLogForms_iff f D n hD _ _ _ _).mpr fun x hx => ?_
  obtain ⟨U₁, hU₁, hx₁, hle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  refine ⟨⟨U₁, hU₁⟩, hle, hx₁, ?_⟩
  have e := totalRestrict_δ (g := gU f D) ((Opens.map (Uc D).ι.base).map (homOfLE hle)).op
    (res D W a)
  rw [res_restrict] at e
  refine AddSubgroup.subset_closure ⟨1, Submodule.mem_top, _,
    Subring.subset_closure (Or.inl (Or.inr ⟨X.presheaf.map (homOfLE hle).op a, rfl⟩)), ?_⟩
  rw [map_one, map_one, one_mul]
  refine Eq.trans ?_ e
  exact ((TB (gU f D)).totalRestrict_incl _ 1 _).symm

/-- `dt/t` is a logarithmic one-form for a local equation `t` of a component of `D`. -/
theorem dlog_mem_relativeLogForms (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ D.support)
    {W : X.affineOpens} {t : Γ(X, W)} (ht : E.idealSheaf.ideal W = Ideal.span {t})
    (s : Γ((Uc D).toScheme, (Uc D).ι ⁻¹ᵁ (W : X.Opens))) (hs : s * res D W t = 1) :
    (asStr s • (show ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece 1).val.obj
      (op ((Uc D).ι ⁻¹ᵁ (W : X.Opens))) from
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials (gU f D))).val.app
        (op ((Uc D).ι ⁻¹ᵁ (W : X.Opens))) ((Scheme.Hom.universalRelativeDerivation (gU f D)).d
          (X := op ((Uc D).ι ⁻¹ᵁ (W : X.Opens))) (res D W t)))) ∈
      relativeLogForms n f D hD ⊤ 1 W := by
  refine (mem_relativeLogForms_iff f D n hD _ _ _ _).mpr fun x hx => ?_
  obtain ⟨U₁, hU₁, hx₁, hle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  let W₁ : X.affineOpens := ⟨U₁, hU₁⟩
  refine ⟨W₁, hle, hx₁, ?_⟩
  refine AddSubgroup.subset_closure ⟨1, Submodule.mem_top, _,
    Subring.subset_closure (Or.inr ⟨E, hE, X.presheaf.map (homOfLE hle).op t, ?_,
      (Uc D).toScheme.presheaf.map ((Opens.map (Uc D).ι.base).map (homOfLE hle)).op s, ?_, rfl⟩),
      ?_⟩
  · rw [← E.idealSheaf.map_ideal hle, ht, Ideal.map_span, Set.image_singleton]
    rfl
  · rw [← res_restrict, ← map_mul, hs, map_one]
  · rw [map_one, map_one, one_mul]
    refine (incl_map_smul _ 1 _ _).trans (congrArg _ ?_)
    exact ((TB (gU f D)).totalRestrict_incl _ 1 _).symm.trans ((totalRestrict_δ _ _).trans
      (congrArg (δ (gU f D) _) (res_restrict D hle t)))

/-- Logarithmic forms are closed under finite sums. -/
theorem sum_mem_relativeLogForms (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData) (p : ℤ) (W : X.Opens) {ι : Type*}
    (s : Finset ι) (ω : ι → ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece p).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W))) (hω : ∀ i ∈ s, ω i ∈ relativeLogForms n f D hD I p W) :
    ∑ i ∈ s, ω i ∈ relativeLogForms n f D hD I p W := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact G1.zero_mem_relativeLogForms n f D hD I p W
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact G1.add_mem_relativeLogForms n f D hD I p (hω a (Finset.mem_insert_self a s))
      (ih fun i hi => hω i (Finset.mem_insert_of_mem hi))

/-- Logarithmic forms are closed under multiplication by natural numbers. -/
theorem nsmul_mem_relativeLogForms (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData) (p : ℤ) (W : X.Opens) (k : ℕ)
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece p).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W))} (hω : ω ∈ relativeLogForms n f D hD I p W) :
    k • ω ∈ relativeLogForms n f D hD I p W := by
  induction k with
  | zero => rw [zero_smul]; exact G1.zero_mem_relativeLogForms n f D hD I p W
  | succ k ih => rw [succ_nsmul]; exact G1.add_mem_relativeLogForms n f D hD I p ih hω

/-- The products `b · dc₁ ∧ ⋯ ∧ dc_q` whose function `b` comes from `W'` when `q = 0`. -/
noncomputable def resMonSet (W' : X.affineOpens) :
    AddSubgroup ((TB (gU f D)).Total (op ((Uc D).ι ⁻¹ᵁ (W' : X.Opens)))) :=
  AddSubgroup.closure {z | ∃ b l, z = mon (gU f D) _ b l ∧ (l = [] → ∃ a, b = res D W' a)}

/-- `resMonSet` is closed under multiplication. -/
theorem mul_mem_resMonSet (W' : X.affineOpens) {z z'}
    (hz : z ∈ resMonSet f D W') (hz' : z' ∈ resMonSet f D W') : z * z' ∈ resMonSet f D W' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, l, rfl, hb⟩ := hz
    induction hz' using AddSubgroup.closure_induction with
    | mem z' hz' =>
      obtain ⟨b', l', rfl, hb'⟩ := hz'
      refine AddSubgroup.subset_closure ⟨b * b', l ++ l', mon_mul b b' l l', fun h => ?_⟩
      obtain ⟨a, rfl⟩ := hb (List.append_eq_nil_iff.mp h).1
      obtain ⟨a', rfl⟩ := hb' (List.append_eq_nil_iff.mp h).2
      exact ⟨a * a', (map_mul _ a a').symm⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

/-- The degree-zero part of an element of `resMonSet` is a function from `W'`. -/
theorem incl_proj_zero_of_mem_resMonSet (W' : X.affineOpens) {z}
    (hz : z ∈ resMonSet f D W') : ∃ a : Γ(X, W'),
      (TB (gU f D)).incl ((0 : ℕ) : ℤ) ((TB (gU f D)).proj _ ((0 : ℕ) : ℤ) z) =
        sm (gU f D) _ (res D W' a) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, l, rfl, hb⟩ := hz
    by_cases hl : l = []
    · subst hl
      obtain ⟨a, rfl⟩ := hb rfl
      refine ⟨a, ?_⟩
      have := incl_proj_mon (g := gU f D) (res D W' a) []
      simpa [mon] using this
    · refine ⟨0, ?_⟩
      rw [proj_mon_of_ne _ _ (fun h => hl (List.length_eq_zero_iff.mp h)), (TB (gU f D)).incl_zero,
        map_zero, map_zero]
  | zero => exact ⟨0, by rw [map_zero, (TB (gU f D)).incl_zero, map_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    exact ⟨a + a', by rw [map_add, (TB (gU f D)).incl_add, ha, ha', map_add, map_add]⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨-a, ?_⟩
    rw [map_neg, map_neg, map_neg, ← ha]
    exact map_neg (DirectSum.of _ _) _

/-- The ring generated by `gens` is contained in `resMonSet`. -/
theorem closure_gens_le_resMonSet (W' : X.affineOpens) {z}
    (hz : z ∈ Subring.closure (gens f D W')) : z ∈ resMonSet f D W' := by
  let R : Subring ((TB (gU f D)).Total (op ((Uc D).ι ⁻¹ᵁ (W' : X.Opens)))) :=
    { carrier := resMonSet f D W'
      mul_mem' := mul_mem_resMonSet f D W'
      one_mem' := AddSubgroup.subset_closure ⟨res D W' 1, [], by simp [mon], fun _ => ⟨1, rfl⟩⟩
      add_mem' := add_mem
      zero_mem' := zero_mem _
      neg_mem' := neg_mem }
  refine (Subring.closure_le (t := R)).mpr ?_ hz
  rintro _ ((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨E, -, t, -, s, -, rfl⟩)
  · exact AddSubgroup.subset_closure ⟨res D W' a, [], by simp [mon], fun _ => ⟨a, rfl⟩⟩
  · exact AddSubgroup.subset_closure ⟨1, [res D W' a], by simp [mon], fun h => (List.cons_ne_nil _
      _ h).elim⟩
  · exact AddSubgroup.subset_closure ⟨s, [res D W' t], by simp [mon], fun h => (List.cons_ne_nil _
      _ h).elim⟩

/-- **Logarithmic functions are functions.** A degree-zero section of `I · Ω^•(log D)` is, near
every point, the restriction of a function in `I`. -/
theorem exists_res_of_mem_relativeLogForms_zero (n : ℕ) [SmoothOfRelativeDimension n f]
    (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData) {W₁ : X.Opens}
    {η : ((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece ((0 : ℕ) : ℤ)).val.obj
      (op ((Uc D).ι ⁻¹ᵁ W₁))} (hη : η ∈ relativeLogForms n f D hD I (0 : ℕ) W₁) {y : X}
    (hy : y ∈ W₁) : ∃ (W'' : X.affineOpens) (h : (W'' : X.Opens) ≤ W₁), y ∈ (W'' : X.Opens) ∧
      ∃ c ∈ I.ideal W'', (TB (gU f D)).incl ((0 : ℕ) : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra (gU f D)).piece ((0 : ℕ) : ℤ)).val.map
          ((Opens.map (Uc D).ι.base).map (homOfLE h)).op η) = sm (gU f D) _ (res D W'' c) := by
  obtain ⟨W'', h, hy'', hb⟩ := (mem_relativeLogForms_iff f D n hD _ _ _ _).mp hη y hy
  refine ⟨W'', h, hy'', ?_⟩
  have key : ∀ z ∈ logClosure f D I W'', ∃ c ∈ I.ideal W'',
      (TB (gU f D)).incl ((0 : ℕ) : ℤ) ((TB (gU f D)).proj _ ((0 : ℕ) : ℤ) z) =
        sm (gU f D) _ (res D W'' c) := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, ζ, hζ, rfl⟩ := hz
      obtain ⟨c, hc⟩ := incl_proj_zero_of_mem_resMonSet f D W'' (closure_gens_le_resMonSet f D W''
          hζ)
      refine ⟨a * c, I.ideal W'' |>.mul_mem_right c ha, ?_⟩
      have e : (TB (gU f D)).proj _ ((0 : ℕ) : ℤ) (sm (gU f D) _ (res D W'' a) * ζ) =
          (show (Stacks.RingedSpace.structureRingSheaf (Uc D).toScheme.toRingedSpace).obj.obj (op _)
            from res D W'' a) • (TB (gU f D)).proj _ ((0 : ℕ) : ℤ) ζ :=
        (congrArg ((TB (gU f D)).proj _ ((0 : ℕ) : ℤ)) (smul_eq_sm_mul _ ζ).symm).trans
          (LinearMap.map_smul _ _ _)
      rw [e, ← sm_mul_incl, hc, ← map_mul, ← map_mul]
    | zero => exact ⟨0, zero_mem _, by rw [map_zero, (TB (gU f D)).incl_zero, map_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, e⟩ := hx
      obtain ⟨c', hc', e'⟩ := hy
      exact ⟨c + c', add_mem hc hc', by rw [map_add, (TB (gU f D)).incl_add, e, e', map_add,
          map_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, e⟩ := hx
      refine ⟨-c, neg_mem hc, ?_⟩
      rw [map_neg, map_neg, map_neg, ← e]
      exact map_neg (DirectSum.of _ _) _
  obtain ⟨c, hc, e⟩ := key _ hb
  exact ⟨c, hc, (congrArg _ ((TB (gU f D)).proj_incl _ _ _)).symm.trans e⟩

end Log

end B1

/-! ### The forms on `U' = X ∖ (D ∪ Supp M)` as a sheaf on `X` -/

section Ambient

variable {X T : Scheme.{u}} (f : X ⟶ T) (D M : Divisor X)

/-- The complement `U = X ∖ D`. -/
abbrev cU : X.Opens := D.supp.compl

/-- The complement `U' = X ∖ (D ∪ Supp M)`. -/
abbrev cU' : X.Opens := (D.supp ⊔ M.supp).compl

/-- `U'` as an open of `U`. -/
abbrev cV : (cU D).toScheme.Opens := (cU D).ι ⁻¹ᵁ cU' D M

/-- The trace `U ∩ W ∩ U'` on `U` of an open `W` of `X`. -/
abbrev OO (W : X.Opens) : (cU D).toScheme.Opens := (cU D).ι ⁻¹ᵁ (W ⊓ cU' D M)

/-- The open of `U` over which the direct image of the forms on `U'` has its sections over `W`. -/
abbrev OA (W : X.Opens) : (cU D).toScheme.Opens :=
  (cV D M).ι ''ᵁ (((cV D M).ι ≫ (cU D).ι) ⁻¹ᵁ W)

/-- `OA D M W` is the open `U ∩ W ∩ U'`. -/
theorem OA_eq (W : X.Opens) : OA D M W = OO D M W := by
  change (cV D M).ι ''ᵁ ((cV D M).ι ⁻¹ᵁ ((cU D).ι ⁻¹ᵁ W)) = (cU D).ι ⁻¹ᵁ W ⊓ (cU D).ι ⁻¹ᵁ cU' D M
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]

/-- The direct image `j'_*Ω^p_{U'}` on `X` of the forms on `U'`. -/
noncomputable abbrev amb (p : ℤ) : X.Modules :=
  (Scheme.Modules.pushforward ((cV D M).ι ≫ (cU D).ι)).obj
    ((Scheme.Modules.restrictFunctor (cV D M).ι).obj
      (Scheme.Hom.relativeDifferentialForms ((cU D).ι ≫ f) p))

/-- The identification of the sections of `j'_*Ω^p_{U'}` over `W` with the forms over
`U ∩ W ∩ U'`. -/
noncomputable def tr (p : ℤ) (W : X.Opens) (x : Γ(amb f D M p, W)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj
      (op (OO D M W)) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.map
    (homOfLE (le_of_eq (OA_eq D M W).symm)).op x

/-- The action of functions on `j'_*Ω^p_{U'}` is through their restriction to `U'`. -/
theorem amb_smul (p : ℤ) {W : X.Opens} (r : X.ringCatSheaf.obj.obj (op W))
    (x : (amb f D M p).val.obj (op W)) :
    r • x = (show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
        (op (OA D M W)) from ((cV D M).ι.appIso (((cV D M).ι ≫ (cU D).ι) ⁻¹ᵁ W)).inv.hom
          ((((cV D M).ι ≫ (cU D).ι).app W).hom r)) •
      (show ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj
        (op (OA D M W)) from x) := rfl

/-- Restriction of a function from `W` to `U ∩ W ∩ U'`. -/
noncomputable abbrev resO (W : X.Opens) (r : Γ(X, W)) : Γ((cU D).toScheme, OO D M W) :=
  ((cU D).ι.app (W ⊓ cU' D M)).hom (X.presheaf.map (homOfLE inf_le_left).op r)

/-- Two consecutive restrictions of a function are one restriction. -/
theorem presheaf_map_map {Y : Scheme.{u}} {A B C : Y.Opensᵒᵖ} (i : A ⟶ B) (j : B ⟶ C)
    (k : A ⟶ C) (a : Y.presheaf.obj A) :
    (Y.presheaf.map j).hom ((Y.presheaf.map i).hom a) = (Y.presheaf.map k).hom a := by
  rw [show k = i ≫ j from Subsingleton.elim _ _, Y.presheaf.map_comp]
  rfl

/-- Two composites of restriction maps with the same source and target are equal. -/
theorem presheaf_map_comp_eq {Y : Scheme.{u}} {A B C E B' : Y.Opensᵒᵖ} (a : A ⟶ B)
    (b : B ⟶ C) (c : C ⟶ E) (d : A ⟶ B') (e : B' ⟶ E) :
    (Y.presheaf.map a ≫ Y.presheaf.map b) ≫ Y.presheaf.map c =
      Y.presheaf.map d ≫ Y.presheaf.map e := by
  rw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
  exact congrArg _ (Subsingleton.elim _ _)

/-- The image of a function on `W` among the functions on `U ∩ W ∩ U'` is `resO D M W`. -/
theorem scal_eq {W : X.Opens} (r : Γ(X, W)) :
    ((cU D).toScheme.presheaf.map (homOfLE (le_of_eq (OA_eq D M W).symm)).op).hom
      (((cV D M).ι.appIso (((cV D M).ι ≫ (cU D).ι) ⁻¹ᵁ W)).inv.hom
        ((((cV D M).ι ≫ (cU D).ι).app W).hom r)) = resO D M W r := by
  have key : (((cV D M).ι ≫ (cU D).ι).app W ≫
      ((cV D M).ι.appIso (((cV D M).ι ≫ (cU D).ι) ⁻¹ᵁ W)).inv ≫
        (cU D).toScheme.presheaf.map (homOfLE (le_of_eq (OA_eq D M W).symm)).op) =
      X.presheaf.map (homOfLE inf_le_left).op ≫ (cU D).ι.app (W ⊓ cU' D M) := by
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Hom.comp_app,
      Scheme.Opens.ι_app, Scheme.Opens.toScheme_presheaf_map]
    erw [Category.id_comp]
    exact presheaf_map_comp_eq _ _ _ _ _
  exact congrArg (fun φ => φ.hom r) key

/-- `tr` is linear over the functions on `W`. -/
theorem tr_smul (p : ℤ) {W : X.Opens} (r : X.ringCatSheaf.obj.obj (op W))
    (x : (amb f D M p).val.obj (op W)) :
    tr f D M p W (r • x) =
      (show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
        (op (OO D M W)) from resO D M W r) • tr f D M p W x := by
  refine (congrArg (tr f D M p W) (amb_smul f D M p r x)).trans ?_
  exact (PresheafOfModules.map_smul _ _ _ _).trans (congrArg (· • _) (scal_eq D M r))

/-- `tr` is additive. -/
theorem tr_add (p : ℤ) {W : X.Opens} (x y : (amb f D M p).val.obj (op W)) :
    tr f D M p W (x + y) = tr f D M p W x + tr f D M p W y :=
  map_add _ x y

/-- The inverse of `tr`. -/
noncomputable def trInv (p : ℤ) (W : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj
      (op (OO D M W))) : Γ(amb f D M p, W) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.map
    (homOfLE (le_of_eq (OA_eq D M W))).op ω

/-- Two consecutive restrictions in a presheaf of modules are one restriction. -/
theorem piece_map_map {Y : Scheme.{u}} {R : (Y.Opens)ᵒᵖ ⥤ RingCat.{u}}
    {A B C : Y.Opensᵒᵖ} (M : PresheafOfModules.{u} R) (i : A ⟶ B)
    (j : B ⟶ C) (k : A ⟶ C) (x : M.obj A) : M.map j (M.map i x) = M.map k x := by
  rw [show k = i ≫ j from Subsingleton.elim _ _, PresheafOfModules.map_comp_apply]

/-- Restriction along an endomorphism of an open is the identity. -/
theorem piece_map_id {Y : Scheme.{u}} {R : (Y.Opens)ᵒᵖ ⥤ RingCat.{u}} {A : Y.Opensᵒᵖ}
    (M : PresheafOfModules.{u} R) (i : A ⟶ A) (x : M.obj A) : M.map i x = x := by
  rw [show i = 𝟙 A from Subsingleton.elim _ _, PresheafOfModules.map_id_apply]

/-- `trInv` is a right inverse of `tr`. -/
theorem tr_trInv (p : ℤ) (W : X.Opens) (ω) : tr f D M p W (trInv f D M p W ω) = ω :=
  (piece_map_map ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val
    (homOfLE (le_of_eq (OA_eq D M W))).op (homOfLE (le_of_eq (OA_eq D M W).symm)).op (𝟙 _) ω).trans
    (piece_map_id _ _ ω)

/-- `trInv` is a left inverse of `tr`. -/
theorem trInv_tr (p : ℤ) (W : X.Opens) (x : Γ(amb f D M p, W)) :
    trInv f D M p W (tr f D M p W x) = x := by
  unfold trInv tr
  exact (piece_map_map ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val
    (homOfLE (le_of_eq (OA_eq D M W).symm)).op (homOfLE (le_of_eq (OA_eq D M W))).op
      (𝟙 (op (OA D M W))) x).trans
    (piece_map_id ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val
      (𝟙 (op (OA D M W))) x)

/-- `tr` is injective. -/
theorem tr_injective (p : ℤ) (W : X.Opens) : Function.Injective (tr f D M p W) :=
  Function.LeftInverse.injective (trInv_tr f D M p W)

/-- `tr` commutes with restriction. -/
theorem tr_restrict (p : ℤ) {W W' : X.Opens} (h : W' ≤ W) (x : Γ(amb f D M p, W)) :
    tr f D M p W' ((amb f D M p).val.map (homOfLE h).op x) =
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.map
        (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right _ h))).op (tr f D M p W x) := by
  let P := ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val
  have hk : OO D M W' ≤ OA D M W :=
    (Scheme.Hom.preimage_mono _ (inf_le_inf_right _ h)).trans (le_of_eq (OA_eq D M W).symm)
  exact (piece_map_map P ((cV D M).ι.opensFunctor.map
      ((Opens.map ((cV D M).ι ≫ (cU D).ι).base).map (homOfLE h))).op
      (homOfLE (le_of_eq (OA_eq D M W').symm)).op (homOfLE hk).op x).trans
    (piece_map_map P (homOfLE (le_of_eq (OA_eq D M W).symm)).op
      (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right _ h))).op (homOfLE hk).op x).symm

end Ambient

/-! ### The sheaf `C^p = 𝒪_X(-M) · Ω^p_X(log D)(-S)` -/

section Cond

variable (n : ℕ) {X T : Scheme.{u}} (f : X ⟶ T) [SmoothOfRelativeDimension n f]
  [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) (hD : D.IsRelativeSNC n f) (S M : Divisor X)

/-- The forms on `U ∩ W ∩ U'` which are, locally on `W`, sums `∑ aᵢ ηᵢ` with `aᵢ` a section of
`𝒪_X(-M)` and `ηᵢ` a section of `Ω^p_X(log D)(-S)`. -/
def Cond (p : ℕ) (W : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op (OO D M W))) : Prop :=
  ∀ x ∈ W, ∃ (W' : X.affineOpens) (h : (W' : X.Opens) ≤ W), x ∈ (W' : X.Opens) ∧
    ∃ (m : ℕ) (g : Fin m → Γ(X, (W' : X.Opens) ⊓ cU' D M))
      (η : Fin m → ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
        (p : ℤ)).val.obj (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens)))),
      (∀ i, ∃ a ∈ (-M).divisorialSubmodule (W' : X.Opens),
        (rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op a =
          (toRationalFunctionsPresheaf X).app (op ((W' : X.Opens) ⊓ cU' D M)) (g i)) ∧
      (∀ i, η i ∈ relativeLogForms n f D hD S.suppIdeal p (W' : X.Opens)) ∧
      (TB ((cU D).ι ≫ f)).incl (p : ℤ)
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
            (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op ω) =
        ∑ i, (TB ((cU D).ι ≫ f)).structureMap (op (OO D M W'))
            ((cU D).ι.app ((W' : X.Opens) ⊓ cU' D M) (g i)) *
          (TB ((cU D).ι ≫ f)).incl (p : ℤ)
            (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
              (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op (η i))

variable {D M} in
/-- A function on `W' ∩ U'` which is a section of `𝒪_X(-M)` over `W'`. -/
def DivCond (W' : X.Opens) (g : Γ(X, W' ⊓ cU' D M)) : Prop :=
  ∃ a ∈ (-M).divisorialSubmodule W',
    (rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op a =
      (toRationalFunctionsPresheaf X).app (op (W' ⊓ cU' D M)) g

omit [SmoothOfRelativeDimension n f] in
/-- `DivCond` is preserved by restriction to a smaller open. -/
theorem DivCond.restrict {W' W'' : X.Opens} (h : W'' ≤ W') {g : Γ(X, W' ⊓ cU' D M)}
    (hg : DivCond (D := D) (M := M) W' g) :
    DivCond (D := D) (M := M) W'' (X.presheaf.map (homOfLE (inf_le_inf_right _ h)).op g) := by
  obtain ⟨a, ha, he⟩ := hg
  refine ⟨(rationalFunctionsPresheaf X).map (homOfLE h).op a, ha.map (homOfLE h), ?_⟩
  have nat := (toRationalFunctionsPresheaf X).naturality (homOfLE (inf_le_inf_right (cU' D M) h)).op
  calc (rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op
        ((rationalFunctionsPresheaf X).map (homOfLE h).op a) =
      (rationalFunctionsPresheaf X).map (homOfLE (inf_le_inf_right (cU' D M) h)).op
        ((rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op a) := rfl
    _ = (rationalFunctionsPresheaf X).map (homOfLE (inf_le_inf_right (cU' D M) h)).op
        ((toRationalFunctionsPresheaf X).app (op (W' ⊓ cU' D M)) g) := by rw [he]
    _ = _ := (congrArg (fun φ => φ.hom g) nat).symm

/-- A representation `ω = ∑ gᵢ ηᵢ` over `U ∩ W' ∩ U'`, `gᵢ` sections of `𝒪_X(-M)` and `ηᵢ`
sections of `Ω^p_X(log D)(-S)` over `W'`. -/
def LocalRep (p : ℕ) (W' : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op (OO D M W'))) : Prop :=
  ∃ (m : ℕ) (g : Fin m → Γ(X, W' ⊓ cU' D M))
    (η : Fin m → ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (p : ℤ)).val.obj (op ((cU D).ι ⁻¹ᵁ W'))),
    (∀ i, DivCond (D := D) (M := M) W' (g i)) ∧
    (∀ i, η i ∈ relativeLogForms n f D hD S.suppIdeal p W') ∧
    (TB ((cU D).ι ≫ f)).incl (p : ℤ) ω =
      ∑ i, (TB ((cU D).ι ≫ f)).structureMap (op (OO D M W')) ((cU D).ι.app (W' ⊓ cU' D M) (g i)) *
        (TB ((cU D).ι ≫ f)).incl (p : ℤ)
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
            (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op (η i))

/-- `Cond` holds if and only if near every point the restriction to some affine open satisfies
`LocalRep`. -/
theorem cond_iff (p : ℕ) (W : X.Opens) (ω) :
    Cond n f D hD S M p W ω ↔ ∀ x ∈ W, ∃ (W' : X.affineOpens) (h : (W' : X.Opens) ≤ W),
      x ∈ (W' : X.Opens) ∧ LocalRep n f D hD S M p W'
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
          (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op ω) := Iff.rfl

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- `incl` commutes with restriction. -/
theorem incl_map {O O' : (cU D).toScheme.Opens} (φ : op O ⟶ op O') (p : ℤ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj (op O)) :
    (TB ((cU D).ι ≫ f)).incl p
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.map φ x) =
      (TB ((cU D).ι ≫ f)).totalRestrict φ ((TB ((cU D).ι ≫ f)).incl p x) :=
  ((TB ((cU D).ι ≫ f)).totalRestrict_incl φ p x).symm

/-- `LocalRep` is preserved by restriction to a smaller open. -/
theorem LocalRep.restrict {p : ℕ} {W' W'' : X.Opens} (h : W'' ≤ W') {ω}
    (hω : LocalRep n f D hD S M p W' ω) :
    LocalRep n f D hD S M p W''
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op ω) := by
  obtain ⟨m, g, η, hg, hη, he⟩ := hω
  refine ⟨m, fun i => X.presheaf.map (homOfLE (inf_le_inf_right _ h)).op (g i),
    fun i => G1.rs f D p h (η i), fun i => (hg i).restrict D M h,
    fun i => G1.relativeLogForms_restrict n f D hD _ _ h (hη i), ?_⟩
  set φ : op (OO D M W') ⟶ op (OO D M W'') :=
    (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op
  have hR : ∀ z, (TB ((cU D).ι ≫ f)).totalRestrictRingHom φ z =
      (TB ((cU D).ι ≫ f)).totalRestrict φ z := fun z =>
    (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply φ z
  rw [incl_map, he, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hR, map_mul, hR, hR]
  refine congrArg₂ (· * ·) (((TB ((cU D).ι ≫ f)).structureMap_naturality φ _).trans
    (congrArg _ (G1.app_restrict (inf_le_inf_right (cU' D M) h) (g i)))) ?_
  refine (incl_map f D φ (p : ℤ) _).symm.trans (congrArg _ ?_)
  let P := ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val
  have hk : OO D M W'' ≤ (cU D).ι ⁻¹ᵁ W' :=
    Scheme.Hom.preimage_mono _ (inf_le_left.trans h)
  exact (piece_map_map P (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op φ (homOfLE hk).op
      (η i)).trans
    (piece_map_map P ((Opens.map (cU D).ι.base).map (homOfLE h)).op
      (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op (homOfLE hk).op (η i)).symm

/-- Zero satisfies `LocalRep`. -/
theorem LocalRep.zero (p : ℕ) (W' : X.Opens) : LocalRep n f D hD S M p W' 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by
    rw [(TB ((cU D).ι ≫ f)).incl_zero, Finset.univ_eq_empty, Finset.sum_empty]⟩

/-- `LocalRep` is closed under addition. -/
theorem LocalRep.add {p : ℕ} {W' : X.Opens} {ω ω'} (hω : LocalRep n f D hD S M p W' ω)
    (hω' : LocalRep n f D hD S M p W' ω') : LocalRep n f D hD S M p W' (ω + ω') := by
  obtain ⟨m, g, η, hg, hη, he⟩ := hω
  obtain ⟨m', g', η', hg', hη', he'⟩ := hω'
  refine ⟨m + m', Fin.append g g', Fin.append η η', fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hg i
    · rw [Fin.append_right]; exact hg' i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hη i
    · rw [Fin.append_right]; exact hη' i
  · rw [(TB ((cU D).ι ≫ f)).incl_add, he, he', Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

/-- `LocalRep` is closed under multiplication by functions on `W'`. -/
theorem LocalRep.smul {p : ℕ} {W' : X.Opens} (c : Γ(X, W')) {ω}
    (hω : LocalRep n f D hD S M p W' ω) :
    LocalRep n f D hD S M p W'
      ((show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
        (op (OO D M W')) from resO D M W' c) • ω) := by
  obtain ⟨m, g, η, hg, hη, he⟩ := hω
  refine ⟨m, g, fun i => (show (Stacks.RingedSpace.structureRingSheaf
      (cU D).toScheme.toRingedSpace).obj.obj (op _) from ((cU D).ι.app W').hom c) • η i, hg,
    fun i => G1.smul_mem_relativeLogForms n f D hD _ _ c (hη i), ?_⟩
  refine (G1.incl_smul_eq f D _ _ ω).trans ?_
  rw [he, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set sm' := (TB ((cU D).ι ≫ f)).structureMap (op (OO D M W'))
  have h1 : (TB ((cU D).ι ≫ f)).incl (p : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op
        ((show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
          (op _) from ((cU D).ι.app W').hom c) • η i)) =
      sm' (resO D M W' c) * (TB ((cU D).ι ≫ f)).incl (p : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
          (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op (η i)) :=
    (congrArg ((TB ((cU D).ι ≫ f)).incl (p : ℤ)) (PresheafOfModules.map_smul _ _ _ _)).trans
      ((G1.incl_smul_eq f D _ _ _).trans
        (congrArg (· * _) (congrArg sm' (G1.app_restrict inf_le_left c))))
  refine Eq.trans ?_ (congrArg (sm' _ * ·) h1).symm
  rw [← mul_assoc, ← mul_assoc]
  exact congrArg (· * _) ((map_mul sm' _ _).symm.trans ((congrArg sm' (mul_comm _ _)).trans
    (map_mul sm' _ _)))

variable {D M} in
/-- Restriction of forms from `U ∩ W ∩ U'` to `U ∩ W' ∩ U'`. -/
noncomputable abbrev rO (p : ℤ) {W W' : X.Opens} (h : W' ≤ W)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj
      (op (OO D M W))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.obj
      (op (OO D M W')) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece p).val.map
    (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op ω

omit [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] [IsNormal X] in
/-- Restriction `rO` is transitive. -/
theorem rO_rO (p : ℤ) {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (ω) :
    rO f p h' (rO f (D := D) (M := M) p h ω) = rO f p (h'.trans h) ω :=
  piece_map_map _ _ _ _ ω

/-- Sections of `C^p` restrict to sections of `C^p`. -/
theorem Cond.restrict {p : ℕ} {W W' : X.Opens} (h : W' ≤ W) {ω}
    (hω : Cond n f D hD S M p W ω) : Cond n f D hD S M p W' (rO f p h ω) := by
  intro x hx
  obtain ⟨W₁, h₁, hx₁, hrep⟩ := hω x (h hx)
  obtain ⟨W₂, hx₂, hle⟩ := G1.exists_affineOpens_le (X := X)
    (show x ∈ (W₁ : X.Opens) ⊓ W' from ⟨hx₁, hx⟩)
  refine ⟨W₂, hle.trans inf_le_right, hx₂, ?_⟩
  have e : rO f (p : ℤ) (hle.trans inf_le_right) (rO f (p : ℤ) h ω) =
      rO f (p : ℤ) (hle.trans inf_le_left) (rO f (p : ℤ) h₁ ω) := by
    rw [rO_rO, rO_rO]
  exact (congrArg (LocalRep n f D hD S M p W₂) e).mpr
    (LocalRep.restrict n f D hD S M (hle.trans inf_le_left) hrep)

/-- A form which is near every point a section of `C^p` is a section of `C^p`. -/
theorem Cond.of_local {p : ℕ} {W : X.Opens} {ω}
    (H : ∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Cond n f D hD S M p V (rO f p h ω)) :
    Cond n f D hD S M p W ω := by
  intro x hx
  obtain ⟨V, hV, hxV, hω⟩ := H x hx
  obtain ⟨W₁, h₁, hx₁, hrep⟩ := hω x hxV
  refine ⟨W₁, h₁.trans hV, hx₁, ?_⟩
  exact (congrArg (LocalRep n f D hD S M p W₁) (rO_rO f (D := D) (M := M) (p : ℤ) hV h₁ ω)).mp hrep

/-- Zero is a section of `C^p`. -/
theorem Cond.zero (p : ℕ) (W : X.Opens) : Cond n f D hD S M p W 0 := by
  intro x hx
  obtain ⟨W', hxW', hle⟩ := G1.exists_affineOpens_le (X := X) hx
  refine ⟨W', hle, hxW', ?_⟩
  exact (congrArg (LocalRep n f D hD S M p W')
    (show rO f (D := D) (M := M) (p : ℤ) hle 0 = 0 from map_zero _)).mpr
    (LocalRep.zero n f D hD S M p _)

/-- Sections of `C^p` are closed under addition. -/
theorem Cond.add {p : ℕ} {W : X.Opens} {ω ω'} (hω : Cond n f D hD S M p W ω)
    (hω' : Cond n f D hD S M p W ω') : Cond n f D hD S M p W (ω + ω') := by
  intro x hx
  obtain ⟨W₁, h₁, hx₁, hr₁⟩ := hω x hx
  obtain ⟨W₂, h₂, hx₂, hr₂⟩ := hω' x hx
  obtain ⟨W₃, hx₃, hle⟩ := G1.exists_affineOpens_le (X := X)
    (show x ∈ (W₁ : X.Opens) ⊓ W₂ from ⟨hx₁, hx₂⟩)
  refine ⟨W₃, hle.trans (inf_le_left.trans h₁), hx₃, ?_⟩
  refine (congrArg (LocalRep n f D hD S M p W₃)
    (show rO f (D := D) (M := M) (p : ℤ) (hle.trans (inf_le_left.trans h₁)) (ω + ω') =
      rO f (p : ℤ) (hle.trans (inf_le_left.trans h₁)) ω +
        rO f (p : ℤ) (hle.trans (inf_le_left.trans h₁)) ω' from map_add _ _ _)).mpr ?_
  refine LocalRep.add n f D hD S M ?_ ?_
  · exact (congrArg (LocalRep n f D hD S M p W₃)
      (rO_rO f (D := D) (M := M) (p : ℤ) h₁ (hle.trans inf_le_left) ω)).mp
      (LocalRep.restrict n f D hD S M (hle.trans inf_le_left) hr₁)
  · exact (congrArg (LocalRep n f D hD S M p W₃)
      (rO_rO f (D := D) (M := M) (p : ℤ) h₂ (hle.trans inf_le_right) ω')).mp
      (LocalRep.restrict n f D hD S M (hle.trans inf_le_right) hr₂)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- `resO` commutes with restriction. -/
theorem resO_restrict {W W' : X.Opens} (h : W' ≤ W) (c : Γ(X, W)) :
    (cU D).toScheme.presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op (resO D M W c) =
      resO D M W' (X.presheaf.map (homOfLE h).op c) := by
  refine (G1.app_restrict (inf_le_inf_right (cU' D M) h) _).trans (congrArg _ ?_)
  exact (presheaf_map_map (homOfLE inf_le_left).op (homOfLE (inf_le_inf_right (cU' D M) h)).op
      (homOfLE (inf_le_left.trans h)).op c).trans
    (presheaf_map_map (homOfLE h).op (homOfLE inf_le_left).op
      (homOfLE (inf_le_left.trans h)).op c).symm

/-- Sections of `C^p` are closed under multiplication by functions on `W`. -/
theorem Cond.smul {p : ℕ} {W : X.Opens} (c : Γ(X, W)) {ω}
    (hω : Cond n f D hD S M p W ω) :
    Cond n f D hD S M p W
      ((show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
        (op (OO D M W)) from resO D M W c) • ω) := by
  intro x hx
  obtain ⟨W₁, h₁, hx₁, hr₁⟩ := hω x hx
  refine ⟨W₁, h₁, hx₁, ?_⟩
  have e : rO f (D := D) (M := M) (p : ℤ) h₁
      ((show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
        (op (OO D M W)) from resO D M W c) • ω) =
      (show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
        (op (OO D M W₁)) from resO D M W₁ (X.presheaf.map (homOfLE h₁).op c)) •
        rO f (p : ℤ) h₁ ω :=
    (PresheafOfModules.map_smul _ _ _ _).trans
      (congrArg (· • rO f (p : ℤ) h₁ ω) (resO_restrict D M h₁ c))
  exact (congrArg (LocalRep n f D hD S M p W₁) e).mpr
    (LocalRep.smul n f D hD S M _ hr₁)

/-- `C^p = 𝒪_X(-M) · Ω^p_X(log D)(-S)` as a subsheaf of `𝒪_X`-modules of `j'_*Ω^p_{U'}`. -/
noncomputable def csub (p : ℕ) : (amb f D M (p : ℤ)).Submodule where
  obj W :=
    { carrier := {x | Cond n f D hD S M p W.unop (tr f D M (p : ℤ) W.unop x)}
      add_mem' := fun {x y} hx hy => by
        change Cond n f D hD S M p W.unop (tr f D M (p : ℤ) W.unop (x + y))
        rw [tr_add]
        exact Cond.add n f D hD S M hx hy
      zero_mem' := by
        change Cond n f D hD S M p W.unop (tr f D M (p : ℤ) W.unop 0)
        rw [show tr f D M (p : ℤ) W.unop 0 = 0 from map_zero _]
        exact Cond.zero n f D hD S M p _
      smul_mem' := fun r x hx => by
        change Cond n f D hD S M p W.unop (tr f D M (p : ℤ) W.unop (r • x))
        rw [tr_smul]
        exact Cond.smul n f D hD S M r hx }
  map {W W'} g x hx := by
    change Cond n f D hD S M p W'.unop (tr f D M (p : ℤ) W'.unop ((amb f D M (p : ℤ)).val.map g x))
    rw [show g = (homOfLE (leOfHom g.unop)).op from Subsingleton.elim _ _]
    exact (congrArg (Cond n f D hD S M p W'.unop)
      (tr_restrict f D M (p : ℤ) (leOfHom g.unop) x)).mpr
      (Cond.restrict n f D hD S M (leOfHom g.unop) hx)
  isSheaf W x hx := by
    change Cond n f D hD S M p W.unop (tr f D M (p : ℤ) W.unop x)
    refine Cond.of_local n f D hD S M fun y hy => ?_
    obtain ⟨V, g, hg, hyV⟩ := hx y hy
    refine ⟨V, leOfHom g, hyV, ?_⟩
    have e := tr_restrict f D M (p : ℤ) (leOfHom g) x
    rw [show g = homOfLE (leOfHom g) from Subsingleton.elim _ _] at hg
    exact (congrArg (Cond n f D hD S M p V) e).mp hg

/-- The `𝒪_X`-module `C^p`. -/
noncomputable abbrev cMod (p : ℕ) : X.Modules := (csub n f D hD S M p).toSheafOfModules

omit [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] [IsNormal X] in
/-- `BrSet` consists of sums of products `b · dc₁ ∧ ⋯ ∧ dc_p`. -/
theorem BrSet_le_monSet (I : X.IdealSheafData) (W' : X.affineOpens) :
    G1.BrSet f D I W' ≤ monSet ((cU D).ι ≫ f) ((cU D).ι ⁻¹ᵁ (W' : X.Opens)) := by
  have hgens : Subring.closure (G1.gens f D W') ≤
      monSubring ((cU D).ι ≫ f) ((cU D).ι ⁻¹ᵁ (W' : X.Opens)) := by
    refine Subring.closure_le.mpr ?_
    rintro z ((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨E, -, t, -, s, -, rfl⟩)
    · exact sm_mem_monSet _
    · exact δ_mem_monSet _
    · exact mul_mem_monSet (sm_mem_monSet _) (δ_mem_monSet _)
  refine AddSubgroup.closure_le _ |>.mpr ?_
  rintro _ ⟨a, -, ζ, hζ, rfl⟩
  exact mul_mem_monSet (sm_mem_monSet _) (hgens hζ)

variable {D M} in
/-- A section over `U ∩ W ∩ U'` which is near `y` a sum of products `b · dc₁ ∧ ⋯ ∧ dc_p`. -/
def NearMon (W : X.Opens)
    (z : (TB ((cU D).ι ≫ f)).Total (op (OO D M W))) (y : X) : Prop :=
  ∃ (W' : X.Opens) (h : W' ≤ W), y ∈ W' ∧
    (TB ((cU D).ι ≫ f)).totalRestrict
      (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op z ∈
      monSet ((cU D).ι ≫ f) (OO D M W')

omit [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] [IsNormal X] in
/-- `NearMon` is closed under addition. -/
theorem NearMon.add {W : X.Opens} {z z' y} (hz : NearMon f (D := D) (M := M) W z y)
    (hz' : NearMon f W z' y) : NearMon f W (z + z') y := by
  obtain ⟨W₁, h₁, hy₁, hm₁⟩ := hz
  obtain ⟨W₂, h₂, hy₂, hm₂⟩ := hz'
  refine ⟨W₁ ⊓ W₂, inf_le_left.trans h₁, ⟨hy₁, hy₂⟩, ?_⟩
  rw [map_add]
  refine add_mem ?_ ?_
  · have := totalRestrict_mem_monSet (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
      (inf_le_inf_right (cU' D M) (inf_le_left : W₁ ⊓ W₂ ≤ W₁)))).op hm₁
    rwa [totalRestrict_totalRestrict] at this
  · have := totalRestrict_mem_monSet (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
      (inf_le_inf_right (cU' D M) (inf_le_right : W₁ ⊓ W₂ ≤ W₂)))).op hm₂
    rwa [totalRestrict_totalRestrict] at this

omit [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] [IsNormal X] in
/-- Zero satisfies `NearMon` at every point of `W`. -/
theorem NearMon.zero {W : X.Opens} {y : X} (hy : y ∈ W) :
    NearMon f (D := D) (M := M) W 0 y :=
  ⟨W, le_rfl, hy, by rw [map_zero]; exact zero_mem _⟩

omit [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] [IsNormal X] in
/-- `NearMon` is closed under multiplication by functions on `U ∩ W ∩ U'`. -/
theorem NearMon.sm_mul {W : X.Opens} {z y} (a : Γ((cU D).toScheme, OO D M W))
    (hz : NearMon f (D := D) (M := M) W z y) :
    NearMon f W ((TB ((cU D).ι ≫ f)).structureMap (op (OO D M W)) a * z) y := by
  obtain ⟨W₁, h₁, hy₁, hm₁⟩ := hz
  refine ⟨W₁, h₁, hy₁, ?_⟩
  set φ : op (OO D M W) ⟶ op (OO D M W₁) :=
    (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h₁))).op
  rw [← (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply φ, map_mul,
    (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply, (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply]
  refine mul_mem_monSet ?_ hm₁
  exact ((TB ((cU D).ι ≫ f)).structureMap_naturality φ a).symm ▸ sm_mem_monSet _

omit [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] [IsNormal X] in
/-- `NearMon` is closed under finite sums. -/
theorem NearMon.sum {W : X.Opens} {y : X} (hy : y ∈ W) {ι : Type*} (s : Finset ι)
    (z : ι → (TB ((cU D).ι ≫ f)).Total (op (OO D M W)))
    (hz : ∀ i ∈ s, NearMon f (D := D) (M := M) W (z i) y) :
    NearMon f W (∑ i ∈ s, z i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact NearMon.zero f D M hy
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hz a (Finset.mem_insert_self a s)).add f D M
      (ih fun i hi => hz i (Finset.mem_insert_of_mem hi))

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The restriction to `U ∩ W₁ ∩ U'` of an `I`-twisted logarithmic form on `W₁` is near every point
of `W₁` a sum of products `b · dc₁ ∧ ⋯ ∧ dc_p`. -/
theorem NearMon.of_relativeLogForms (I : X.IdealSheafData) {p : ℕ} {W₁ : X.Opens}
    {η : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₁))} (hη : η ∈ relativeLogForms n f D hD I p W₁) {y : X} (hy : y ∈ W₁) :
    NearMon f (D := D) (M := M) W₁ ((TB ((cU D).ι ≫ f)).incl (p : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op η)) y := by
  obtain ⟨W'', hW'', hy'', hb⟩ := (G1.mem_relativeLogForms_iff' n f D hD I p W₁ η).1 hη y hy
  refine ⟨W'', hW'', hy'', ?_⟩
  let P := ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val
  have hk : OO D M W'' ≤ (cU D).ι ⁻¹ᵁ W₁ := Scheme.Hom.preimage_mono _ (inf_le_left.trans hW'')
  have e := (incl_map f D (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
      (inf_le_inf_right (cU' D M) hW''))).op (p : ℤ) _).symm.trans
    ((congrArg ((TB ((cU D).ι ≫ f)).incl (p : ℤ))
      ((piece_map_map P (homOfLE (Scheme.Hom.preimage_mono (cU D).ι inf_le_left)).op
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_inf_right (cU' D M) hW''))).op
        (homOfLE hk).op η).trans
      (piece_map_map P ((Opens.map (cU D).ι.base).map (homOfLE hW'')).op
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι inf_le_left)).op (homOfLE hk).op η).symm)).trans
      (incl_map f D (homOfLE (Scheme.Hom.preimage_mono (cU D).ι inf_le_left)).op (p : ℤ) _))
  rw [e]
  exact totalRestrict_mem_monSet _ (BrSet_le_monSet f D I W'' hb)

/-- The sections of `C^•` are locally sums of products `b · dc₁ ∧ ⋯ ∧ dc_p`. -/
theorem Cond.exists_monSet {p : ℕ} {W : X.Opens} {ω} (hω : Cond n f D hD S M p W ω)
    {y : X} (hy : y ∈ W) : ∃ (W' : X.Opens) (h : W' ≤ W), y ∈ W' ∧
      (TB ((cU D).ι ≫ f)).incl (p : ℤ) (rO f p h ω) ∈ monSet ((cU D).ι ≫ f) (OO D M W') := by
  obtain ⟨W₁, h₁, hy₁, m, g, η, -, hη, he⟩ := hω y hy
  have hnm : NearMon f (D := D) (M := M) (W₁ : X.Opens)
      ((TB ((cU D).ι ≫ f)).incl (p : ℤ) (rO f p h₁ ω)) y := by
    rw [he]
    exact NearMon.sum f D M hy₁ _ _ fun i _ =>
      NearMon.sm_mul f D M _ (NearMon.of_relativeLogForms n f D hD M _ (hη i) hy₁)
  obtain ⟨W', h', hy', hm⟩ := hnm
  refine ⟨W', h'.trans h₁, hy', ?_⟩
  rw [← rO_rO f (D := D) (M := M) (p : ℤ) h₁ h', incl_map]
  exact hm

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Restricting a representation `∑ gᵢ ηᵢ` to a smaller open. -/
theorem sum_rep_restrict {p : ℕ} {W' W'' : X.Opens} (h : W'' ≤ W') {m : ℕ}
    (g : Fin m → Γ(X, W' ⊓ cU' D M))
    (η : Fin m → ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (p : ℤ)).val.obj (op ((cU D).ι ⁻¹ᵁ W')))
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op (OO D M W'))}
    (he : (TB ((cU D).ι ≫ f)).incl (p : ℤ) ω =
      ∑ i, (TB ((cU D).ι ≫ f)).structureMap (op (OO D M W')) ((cU D).ι.app (W' ⊓ cU' D M) (g i)) *
        (TB ((cU D).ι ≫ f)).incl (p : ℤ)
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
            (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op (η i))) :
    (TB ((cU D).ι ≫ f)).incl (p : ℤ) (rO f (D := D) (M := M) p h ω) =
      ∑ i, (TB ((cU D).ι ≫ f)).structureMap (op (OO D M W''))
          ((cU D).ι.app (W'' ⊓ cU' D M) (X.presheaf.map (homOfLE (inf_le_inf_right _ h)).op (g
              i))) *
        (TB ((cU D).ι ≫ f)).incl (p : ℤ)
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
            (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_left.trans h))).op (η i)) := by
  set φ : op (OO D M W') ⟶ op (OO D M W'') :=
    (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op
  have hR : ∀ z, (TB ((cU D).ι ≫ f)).totalRestrictRingHom φ z =
      (TB ((cU D).ι ≫ f)).totalRestrict φ z := fun z =>
    (TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply φ z
  rw [incl_map, he, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hR, map_mul, hR, hR]
  refine congrArg₂ (· * ·) (((TB ((cU D).ι ≫ f)).structureMap_naturality φ _).trans
    (congrArg _ (G1.app_restrict (inf_le_inf_right (cU' D M) h) (g i)))) ?_
  refine (incl_map f D φ (p : ℤ) _).symm.trans (congrArg _ ?_)
  exact piece_map_map _ _ _ _ (η i)

end Cond

/-! ### The complex `C^•` with the connection `∇ = d - c du ∧` -/

section TwistedComplex

variable (n : ℕ) {X T : Scheme.{u}} (f : X ⟶ T) [SmoothOfRelativeDimension n f]
  [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) (hD : D.IsRelativeSNC n f) (S M : Divisor X)
  (uu cc : Γ(X, cU' D M))

variable {D M} in
/-- The restriction of a function on `U'` to `U ∩ W ∩ U'`. -/
noncomputable abbrev resU (W : X.Opens) (a : Γ(X, cU' D M)) : Γ((cU D).toScheme, OO D M W) :=
  (cU D).ι.app (W ⊓ cU' D M) (X.presheaf.map (homOfLE inf_le_right).op a)

/-- The exact one-form `d a` of a function on an open of `U`, of degree one. -/
noncomputable abbrev dF (O : (cU D).toScheme.Opens) (a : Γ((cU D).toScheme, O)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj (op O) :=
  (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials ((cU D).ι ≫ f))).val.app
    (op O) ((Scheme.Hom.universalRelativeDerivation ((cU D).ι ≫ f)).d (X := op O) a)

/-- The connection form `θ = c du` on `U ∩ W ∩ U'`. -/
noncomputable def θW (W : X.Opens) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op (OO D M W)) :=
  (show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
    (op (OO D M W)) from resU W cc) • dF f D (OO D M W) (resU W uu)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- In the total ring of forms, `θ = c du`. -/
theorem incl_θW (W : X.Opens) :
    (TB ((cU D).ι ≫ f)).incl 1 (θW f D M uu cc W) =
      sm ((cU D).ι ≫ f) (OO D M W) (resU W cc) * δ ((cU D).ι ≫ f) (OO D M W) (resU W uu) :=
  (sm_mul_incl (g := (cU D).ι ≫ f) (resU W cc) 1 _).symm

/-- The connection `∇` on the sections of `j'_*Ω^p_{U'}` over `W`. -/
noncomputable def nabA (p : ℕ) (W : X.Opens) (x : Γ(amb f D M (p : ℤ), W)) :
    Γ(amb f D M ((p + 1 : ℕ) : ℤ), W) :=
  trInv f D M ((p + 1 : ℕ) : ℤ) W (nab ((cU D).ι ≫ f) p (θW f D M uu cc W) (tr f D M (p : ℤ) W x))

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Under `tr`, `nabA` is the twisted differential `nab` with connection form `θ = c du`. -/
theorem tr_nabA (p : ℕ) (W : X.Opens) (x : Γ(amb f D M (p : ℤ), W)) :
    tr f D M ((p + 1 : ℕ) : ℤ) W (nabA f D M uu cc p W x) =
      nab ((cU D).ι ≫ f) p (θW f D M uu cc W) (tr f D M (p : ℤ) W x) :=
  tr_trInv f D M _ W _

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- `resU` commutes with restriction. -/
theorem resU_restrict {W W' : X.Opens} (h : W' ≤ W) (a : Γ(X, cU' D M)) :
    (cU D).toScheme.presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) h))).op (resU W a) =
      resU W' a := by
  refine (G1.app_restrict (inf_le_inf_right (cU' D M) h) _).trans (congrArg _ ?_)
  exact presheaf_map_map _ _ _ a

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- `dF` commutes with restriction. -/
theorem dF_restrict {O O' : (cU D).toScheme.Opens} (φ : op O ⟶ op O')
    (a : Γ((cU D).toScheme, O)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.map φ (dF f D O a) =
      dF f D O' ((cU D).toScheme.presheaf.map φ a) :=
  (PresheafOfModules.naturality_apply
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials ((cU D).ι ≫ f))).val φ
        _).symm.trans (congrArg _
      ((Scheme.Hom.universalRelativeDerivation ((cU D).ι ≫ f)).d_map φ a).symm)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The connection form `θ` restricts to the connection form `θ`. -/
theorem θW_restrict {W W' : X.Opens} (h : W' ≤ W) :
    rO f (D := D) (M := M) 1 h (θW f D M uu cc W) = θW f D M uu cc W' := by
  unfold θW
  refine (PresheafOfModules.map_smul _ _ _ _).trans ?_
  exact congrArg₂ (· • ·) (resU_restrict D M h cc)
    ((dF_restrict f D _ _).trans (congrArg _ (resU_restrict D M h uu)))

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- `nabA` commutes with restriction. -/
theorem nabA_restrict (p : ℕ) {W W' : X.Opens} (h : W' ≤ W) (x : Γ(amb f D M (p : ℤ), W)) :
    nabA f D M uu cc p W' ((amb f D M (p : ℤ)).val.map (homOfLE h).op x) =
      (amb f D M ((p + 1 : ℕ) : ℤ)).val.map (homOfLE h).op (nabA f D M uu cc p W x) := by
  refine tr_injective f D M _ W' ?_
  refine (tr_nabA f D M uu cc p W' _).trans ?_
  refine (congrArg (nab ((cU D).ι ≫ f) p (θW f D M uu cc W')) (tr_restrict f D M (p : ℤ) h
      x)).trans ?_
  refine (congrArg (fun θ => nab ((cU D).ι ≫ f) p θ _) (θW_restrict f D M uu cc h).symm).trans ?_
  refine (nab_map _ p _ _).symm.trans ?_
  refine (congrArg (rO f (D := D) (M := M) ((p + 1 : ℕ) : ℤ) h) (tr_nabA f D M uu cc p W
      x).symm).trans ?_
  exact (tr_restrict f D M _ h _).symm

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- `nabA` is additive. -/
theorem nabA_add (p : ℕ) (W : X.Opens) (x y : Γ(amb f D M (p : ℤ), W)) :
    nabA f D M uu cc p W (x + y) = nabA f D M uu cc p W x + nabA f D M uu cc p W y := by
  refine tr_injective f D M _ W ?_
  refine (tr_nabA f D M uu cc p W _).trans ?_
  refine (congrArg (nab ((cU D).ι ≫ f) p (θW f D M uu cc W)) (tr_add f D M (p : ℤ) x y)).trans ?_
  refine (nab_add p _ _ _).trans ?_
  refine Eq.trans ?_ (tr_add f D M _ _ _).symm
  exact congrArg₂ (· + ·) (tr_nabA f D M uu cc p W x).symm (tr_nabA f D M uu cc p W y).symm

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The image in `𝒪(U ∩ W ∩ U')` of a section of `f⁻¹𝒪_T` over `W` comes from a section of
`(j ≫ f)⁻¹𝒪_T`. -/
theorem resO_inverseImage (W : X.Opens)
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj T.sheaf).obj.obj (op W)) :
    resO D M W (((inverseImageStructureMap f).hom.app (op W)).hom a) =
      ((inverseImageStructureMap ((cU D).ι ≫ f)).hom.app (op (OO D M W))).hom
        ((((TopCat.Sheaf.pullback CommRingCat.{u} ((cU D).ι ≫ f).base).obj T.sheaf).obj.map
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι inf_le_left)).op).hom
          (((G1.phiS f (cU D)).hom.app (op W)).hom a)) := by
  have nat := congrArg (fun h => h.hom (((G1.phiS f (cU D)).hom.app (op W)).hom a))
    ((inverseImageStructureMap ((cU D).ι ≫ f)).hom.naturality
      (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left : W ⊓ cU' D M ≤ W))).op)
  refine Eq.trans ?_ nat.symm
  refine Eq.trans ?_ (congrArg ((cU D).toScheme.presheaf.map
    (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left : W ⊓ cU' D M ≤ W))).op).hom
      (G1.phiS_apply f (cU D) a).symm)
  exact (G1.app_restrict inf_le_left _).symm

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- `nabA` is linear over `f⁻¹𝒪_T`. -/
theorem nabA_smul (p : ℕ) (W : X.Opens)
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj T.sheaf).obj.obj (op W))
    (x : (amb f D M (p : ℤ)).val.obj (op W)) :
    nabA f D M uu cc p W ((show X.ringCatSheaf.obj.obj (op W) from
        ((inverseImageStructureMap f).hom.app (op W)).hom a) • x) =
      (show X.ringCatSheaf.obj.obj (op W) from
        ((inverseImageStructureMap f).hom.app (op W)).hom a) •
        (show (amb f D M ((p + 1 : ℕ) : ℤ)).val.obj (op W) from nabA f D M uu cc p W x) := by
  refine tr_injective f D M _ W ?_
  refine (tr_nabA f D M uu cc p W _).trans ?_
  refine (congrArg (nab ((cU D).ι ≫ f) p (θW f D M uu cc W)) (tr_smul f D M (p : ℤ) _ x)).trans ?_
  refine Eq.trans ?_ (tr_smul f D M _ _ _).symm
  have e := resO_inverseImage f D M W a
  refine (congrArg (fun r => nab ((cU D).ι ≫ f) p (θW f D M uu cc W)
    ((show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
      (op (OO D M W)) from r) • tr f D M (p : ℤ) W x)) e).trans ?_
  refine (nab_smul_base p _ _ _).trans ?_
  refine (congrArg (fun r => (show (Stacks.RingedSpace.structureRingSheaf
      (cU D).toScheme.toRingedSpace).obj.obj (op (OO D M W)) from r) • _) e.symm).trans ?_
  exact congrArg _ (tr_nabA f D M uu cc p W x).symm

/-- `∇` preserves `C^•`. -/
def NabStable : Prop :=
  ∀ (p : ℕ) (W : X.Opens) ω, Cond n f D hD S M p W ω →
    Cond n f D hD S M (p + 1) W (nab ((cU D).ι ≫ f) p (θW f D M uu cc W) ω)

/-- The sheaf `C^p` read over `f⁻¹𝒪_T`. -/
noncomputable abbrev cX (p : ℕ) :
    SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj T.sheaf)) :=
  (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap f))).obj (cMod n f D hD S M p)

/-- The connection `∇ : C^p ⟶ C^{p+1}`, a morphism of sheaves of `f⁻¹𝒪_T`-modules. -/
noncomputable def cD (hst : NabStable n f D hD S M uu cc) (p : ℕ) :
    cX n f D hD S M p ⟶ cX n f D hD S M (p + 1) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun x => ⟨nabA f D M uu cc p W.unop
        x.1,
            (congrArg (Cond n f D hD S M (p + 1) W.unop) (tr_nabA f D M uu cc p W.unop x.1)).mpr
              (hst p W.unop _ x.2)⟩)
          (fun x y => Subtype.ext (nabA_add f D M uu cc p W.unop x.1 y.1)))
      naturality := fun {W W'} g => by
        ext x
        refine Subtype.ext ?_
        rw [show g = (homOfLE (leOfHom g.unop)).op from Subsingleton.elim _ _]
        exact nabA_restrict f D M uu cc p (leOfHom g.unop) x.1 }
    (fun W a x => Subtype.ext (nabA_smul f D M uu cc p W.unop a x.1))⟩

/-- The sections of `C^•` are, locally, sums of products `b · dc₁ ∧ ⋯ ∧ dc_p`. -/
def LocMon : Prop :=
  ∀ (p : ℕ) (W : X.Opens) ω, Cond n f D hD S M p W ω → ∀ y ∈ W, ∃ (W' : X.Opens) (h : W' ≤ W),
    y ∈ W' ∧ (TB ((cU D).ι ≫ f)).incl (p : ℤ) (rO f p h ω) ∈ monSet ((cU D).ι ≫ f) (OO D M W')

/-- If the sections of `C^•` are locally sums of products `b · dc₁ ∧ ⋯ ∧ dc_p` and `dc ∧ du = 0`,
then `∇ ∘ ∇ = 0` on `C^p`. -/
theorem nab_nab_eq_zero (hloc : LocMon n f D hD S M)
    (hcu : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M W) (resU W cc) *
      δ ((cU D).ι ≫ f) (OO D M W) (resU W uu) = 0)
    (p : ℕ) (W : X.Opens) (ω) (hω : Cond n f D hD S M p W ω) :
    nab ((cU D).ι ≫ f) (p + 1) (θW f D M uu cc W)
      (nab ((cU D).ι ≫ f) p (θW f D M uu cc W) ω) = 0 := by
  choose W' hW' hyW' hmon using hloc p W ω hω
  refine piece_ext (g := (cU D).ι ≫ f) _ (fun y : {y // y ∈ W} => OO D M (W' y.1 y.2))
    (fun y => homOfLE (Scheme.Hom.preimage_mono _ (inf_le_inf_right (cU' D M) (hW' y.1 y.2))))
    ?_ _ _ fun y => ?_
  · intro z hz
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(cU D).ι z, hz.1⟩, ?_⟩
    exact ⟨hyW' _ hz.1, hz.2⟩
  · refine ((nab_map _ (p + 1) _ _).trans ?_).trans (map_zero _).symm
    refine (congrArg₂ (nab ((cU D).ι ≫ f) (p + 1)) (θW_restrict f D M uu cc (hW' y.1 y.2))
      (nab_map _ p _ _)).trans ?_
    refine (congrArg (fun θ => nab ((cU D).ι ≫ f) (p + 1) (θW f D M uu cc _)
      (nab ((cU D).ι ≫ f) p θ _)) (θW_restrict f D M uu cc (hW' y.1 y.2))).trans ?_
    exact nab_nab_of_mem p _ _ (hcu _) _ (incl_θW f D M uu cc _) _ (hmon y.1 y.2)

/-- If the sections of `C^•` are locally sums of products `b · dc₁ ∧ ⋯ ∧ dc_p` and `dc ∧ du = 0`,
then `nabA ∘ nabA = 0` on `C^p`. -/
theorem nabA_nabA_eq_zero (hloc : LocMon n f D hD S M)
    (hcu : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M W) (resU W cc) *
      δ ((cU D).ι ≫ f) (OO D M W) (resU W uu) = 0)
    (p : ℕ) (W : X.Opens) (x : Γ(amb f D M (p : ℤ), W))
    (hx : Cond n f D hD S M p W (tr f D M (p : ℤ) W x)) :
    nabA f D M uu cc (p + 1) W (nabA f D M uu cc p W x) = 0 := by
  refine tr_injective f D M _ W ?_
  refine (tr_nabA f D M uu cc (p + 1) W _).trans ?_
  refine (congrArg _ (tr_nabA f D M uu cc p W x)).trans ?_
  exact (nab_nab_eq_zero n f D hD S M uu cc hloc hcu p W _ hx).trans (map_zero _).symm

/-- The complex `C^•` with differential `∇`. -/
noncomputable def cCx (hst : NabStable n f D hD S M uu cc) (hloc : LocMon n f D hD S M)
    (hcu : ∀ W : X.Opens, δ ((cU D).ι ≫ f) (OO D M W) (resU W cc) *
      δ ((cU D).ι ≫ f) (OO D M W) (resU W uu) = 0) :
    CochainComplex (SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj T.sheaf))) ℕ :=
  CochainComplex.of (cX n f D hD S M) (cD n f D hD S M uu cc hst) (fun p => by
    ext W x
    exact Subtype.ext (nabA_nabA_eq_zero n f D hD S M uu cc hloc hcu p W.unop x.1 x.2))

/-- The differential of `cCx` in degree `p` is `cD`. -/
theorem cCx_d (hst hloc hcu) (p : ℕ) :
    (cCx n f D hD S M uu cc hst hloc hcu).d p (p + 1) = cD n f D hD S M uu cc hst p :=
  CochainComplex.of_d _ _ p

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- **The differential formula.** If `c · (N u) = 1`, then
`N u · ∇ω = N u · dω - du ∧ ω`. -/
theorem nsmul_mul_incl_nab (N : ℕ) (hcc : cc * ((N : Γ(X, cU' D M)) * uu) = 1) (p : ℕ)
    (W : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op (OO D M W))) :
    N • ((TB ((cU D).ι ≫ f)).structureMap (op (OO D M W)) (resU W uu) *
        (TB ((cU D).ι ≫ f)).incl ((p + 1 : ℕ) : ℤ) (nab ((cU D).ι ≫ f) p (θW f D M uu cc W) ω)) =
      N • ((TB ((cU D).ι ≫ f)).structureMap (op (OO D M W)) (resU W uu) *
        (TB ((cU D).ι ≫ f)).incl ((p + 1 : ℕ) : ℤ)
          (((Scheme.Hom.deRhamComplex ((cU D).ι ≫ f)).d p (p + 1)).val.app (op (OO D M W)) ω)) -
      (TB ((cU D).ι ≫ f)).incl 1 (dF f D (OO D M W) (resU W uu)) *
        (TB ((cU D).ι ≫ f)).incl (p : ℤ) ω := by
  let φ : Γ(X, cU' D M) →+* Γ((cU D).toScheme, OO D M W) :=
    ((cU D).ι.app (W ⊓ cU' D M)).hom.comp (X.presheaf.map (homOfLE inf_le_right).op).hom
  have h1 : resU W cc * ((N : Γ((cU D).toScheme, OO D M W)) * resU W uu) = 1 := by
    have := congrArg φ hcc
    rwa [map_mul, map_mul, map_natCast, map_one] at this
  set sm' := (TB ((cU D).ι ≫ f)).structureMap (op (OO D M W))
  rw [incl_nab, Δ_incl, incl_θW, mul_sub, smul_sub]
  congr 1
  change N • (sm' (resU W uu) * (sm' (resU W cc) * δ ((cU D).ι ≫ f) (OO D M W) (resU W uu) *
    (TB ((cU D).ι ≫ f)).incl (p : ℤ) ω)) = δ ((cU D).ι ≫ f) (OO D M W) (resU W uu) *
      (TB ((cU D).ι ≫ f)).incl (p : ℤ) ω
  rw [nsmul_eq_mul, ← map_natCast sm' N]
  have h2 : sm' (N : Γ((cU D).toScheme, OO D M W)) * sm' (resU W uu) * sm' (resU W cc) = 1 :=
    ((congrArg (· * sm' (resU W cc)) (map_mul sm' _ _).symm).trans (map_mul sm' _ _).symm).trans
      ((congrArg sm' ((mul_comm _ _).trans h1)).trans (map_one sm'))
  simp only [← mul_assoc]
  exact (congrArg (fun z => z * δ ((cU D).ι ≫ f) (OO D M W) (resU W uu) *
    (TB ((cU D).ι ≫ f)).incl (p : ℤ) ω) h2).trans (congrArg (· * _) (one_mul _))

end TwistedComplex

/-! ### Functions without zeros or poles -/

section Units

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- **Algebraic Hartogs for units.** A function on `W` which is the restriction of a rational
function `φ` with `v_E(φ) = 0` for every prime divisor `E` meeting `W` is a unit. -/
theorem isUnit_of_ord_eq_zero {W : X.Opens} (a : Γ(X, W)) (φ : (RationalFunctions X)ˣ)
    (ha : (toRationalFunctionsPresheaf X).app (op W) a =
      (rationalFunctionsPresheaf X).map (homOfLE le_top).op
        ((rationalFunctionsPresheafTopEquiv X).symm φ))
    (hord : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ W).Nonempty → E.ord φ = 0) :
    IsUnit a := by
  have hdiv : (0 : Divisor X).IsDivisorialSection W
      ((rationalFunctionsPresheaf X).map (homOfLE le_top).op
        ((rationalFunctionsPresheafTopEquiv X).symm ↑φ⁻¹)) := by
    intro E hE
    refine Or.inr ?_
    have h1 := E.valuation_component φ⁻¹
    rw [MMP.Mori.PrimeDivisor.ord_inv, hord E hE, neg_zero] at h1
    rw [DivisorWithCoeffs.coeff_zero, neg_zero]
    exact h1.ge
  obtain ⟨s, hs⟩ := hdiv.exists_eq
  refine IsUnit.of_mul_eq_one s (toRationalFunctionsPresheaf_app_injective W ?_)
  rw [map_mul, map_one, ha, hs]
  funext Z
  change (φ : RationalFunctions X) Z.1 * (↑φ⁻¹ : RationalFunctions X) Z.1 = 1
  rw [← Pi.mul_apply, Units.mul_inv]
  rfl

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A prime divisor meeting the complement of `Supp D` has coefficient zero in `D`. -/
theorem coeff_eq_zero_of_meets {D : Divisor X} {W : X.Opens}
    (hW : W ≤ D.supp.compl) {E : MMP.Mori.PrimeDivisor X} (hE : (E.support ∩ W).Nonempty) :
    D E = 0 := by
  by_contra h
  obtain ⟨x, hxE, hxW⟩ := hE
  exact hW hxW (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, h, hxE⟩)

end Units

/-! ### Charts for the ideal of a subdivisor of a simple normal crossing divisor -/

section SChart

variable {X : Scheme.{u}}

/-- If the generic point of a prime divisor `E` lies on a prime divisor `P`, then `E = P`. -/
theorem eq_of_genericPoint_mem_support {E P : MMP.Mori.PrimeDivisor X}
    (hE : E.genericPoint ∈ P.support) : E = P := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
  have hle : E.genericPoint ≤ P.genericPoint := specializes_iff_mem_closure.mpr hE
  by_contra hne
  have hlt : E.genericPoint < P.genericPoint := lt_of_le_not_ge hle fun h =>
    hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (Specializes.antisymm (show E.genericPoint ⤳ P.genericPoint from h)
        (show P.genericPoint ⤳ E.genericPoint from hle)).eq)
  have h2 := Order.coheight_add_one_le hlt
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint,
    MMP.Mori.PrimeDivisor.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The ideal of a prime divisor on an affine open is radical. -/
theorem isRadical_idealSheaf_ideal (E : MMP.Mori.PrimeDivisor X) (W : X.affineOpens) :
    (E.idealSheaf.ideal W).IsRadical := by
  have := E.integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E.idealSheaf _ rfl]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- The ideal of an ideal sheaf on an affine open disjoint from its support is the unit ideal. -/
theorem ideal_eq_top_of_disjoint (I : X.IdealSheafData) (W : X.affineOpens)
    (h : ∀ y ∈ (W : X.Opens), y ∉ I.support) : I.ideal W = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let P : PrimeSpectrum Γ(X, W) := ⟨m, hm.isPrime⟩
  have hPW : W.2.fromSpec P ∈ (W : X.Opens) := W.2.range_fromSpec.le ⟨P, rfl⟩
  refine h _ hPW ?_
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hPW]
  have : W.2.fromSpec P ∈ W.2.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal W : Set Γ(X, W)) :=
    ⟨P, hle, rfl⟩
  exact ((IsAffineOpen.fromSpec_image_zeroLocus W.2 (I.ideal W : Set Γ(X, W))).le this).1

/-- If `∏ tᵢ` is not invertible at `y`, then some factor `tᵢ` is not invertible at `y`. -/
theorem notMem_basicOpen_of_prod {W : X.Opens} {ι : Type*} (s : Finset ι)
    (t : ι → Γ(X, W)) {y : X} (hy : y ∈ W) (h : y ∉ X.basicOpen (∏ i ∈ s, t i)) :
    ∃ i ∈ s, y ∉ X.basicOpen (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.basicOpen_one] at h
    exact absurd hy h
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul] at h
    by_cases hya : y ∈ X.basicOpen (t a)
    · obtain ⟨i, hi, hyi⟩ := ih fun h' => h ⟨hya, h'⟩
      exact ⟨i, Finset.mem_insert_of_mem hi, hyi⟩
    · exact ⟨a, Finset.mem_insert_self a s, hya⟩

/-- If `I` is generated by `t` on an affine open `W` and `t` is not invertible at `y ∈ W`, then `y`
lies in the support of `I`. -/
theorem mem_support_of_ideal_eq_span {I : X.IdealSheafData} {W : X.affineOpens}
    {t : Γ(X, W)} (ht : I.ideal W = Ideal.span {t}) {y : X} (hy : y ∈ (W : X.Opens))
    (hyt : y ∉ X.basicOpen t) : y ∈ I.support := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hy, ht, Scheme.mem_zeroLocus_iff]
  intro b hb hyb
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  rw [Scheme.basicOpen_mul] at hyb
  exact hyt hyb.2

/-- A section of `I` on an affine open `W` is not invertible at any point of `W` in the support of
`I`. -/
theorem notMem_basicOpen_of_mem_support {I : X.IdealSheafData} {W : X.affineOpens}
    {y : X} (hy : y ∈ (W : X.Opens)) (hI : y ∈ I.support) {a : Γ(X, W)} (ha : a ∈ I.ideal W) :
    y ∉ X.basicOpen a := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hy, Scheme.mem_zeroLocus_iff] at hI
  exact hI a ha

/-- On a chart of a simple normal crossing divisor `D`, every component of `D` meeting the chart
is one of the coordinate components. -/
theorem exists_eq_of_mem_chart {D : Divisor X} {W : X.affineOpens} {n r : ℕ}
    (t : Fin n → Γ(X, W)) (hr : r ≤ n) (j : Fin r → MMP.Mori.PrimeDivisor X)
    (hjD : ∀ i, (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (hDW : D.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)})
    {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ D.support) {y : X} (hyW : y ∈ (W : X.Opens))
    (hyE : y ∈ E.support) : ∃ i, j i = E := by
  have hη : E.genericPoint ∈ (W : X.Opens) := E.genericPoint_mem_of_nonempty ⟨y, hyE, hyW⟩
  have hηE : E.genericPoint ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hηD : E.genericPoint ∈ D.suppIdeal.support := by
    change E.genericPoint ∈ ((Scheme.IdealSheafData.vanishingIdeal D.supp).support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact MMP.Mori.DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE) hηE
  have h1 := notMem_basicOpen_of_mem_support hη hηD (a := ∏ i, t (Fin.castLE hr i))
    (by rw [hDW]; exact Ideal.mem_span_singleton_self _)
  obtain ⟨i, -, hi⟩ := notMem_basicOpen_of_prod Finset.univ _ hη h1
  exact ⟨i, (eq_of_genericPoint_mem_support (mem_support_of_ideal_eq_span (hjD i) hη hi)).symm⟩

/-- The ideal of a finite infimum of ideal sheaves on an affine open is the infimum of their
ideals. -/
theorem finsetInf_ideal {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (W : X.affineOpens) : (s.inf I).ideal W = s.inf fun i => (I i).ideal W := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.inf_insert, ← ih]
    rfl

/-- **Charts for a subdivisor.** If every component of `S` is a component of the relative simple
normal crossing divisor `D`, every point has an affine neighbourhood on which the ideal of the
support of `S` is generated by a product of local equations of components of `D`. -/
theorem exists_chart_suppIdeal (n : ℕ) {T : Scheme.{u}} (f : X ⟶ T)
    [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] (D S : Divisor X)
    (hD : D.IsRelativeSNC n f) (hSD : ∀ E ∈ S.support, E ∈ D.support) (x : X) :
    ∃ (Wc : X.affineOpens) (r : ℕ) (j : Fin r → MMP.Mori.PrimeDivisor X)
      (t : Fin r → Γ(X, Wc)), x ∈ (Wc : X.Opens) ∧
        (∀ i, j i ∈ D.support ∧ (j i).idealSheaf.ideal Wc = Ideal.span {t i}) ∧
        S.suppIdeal.ideal Wc = Ideal.span {∏ i, t i} := by
  classical
  obtain ⟨W, Vb, e, t, hxW, hb, r, hr, j, -, hjD, hDW⟩ := hD.2 x
  let := (f.appLE Vb W e).hom.toAlgebra
  obtain ⟨b, hb⟩ := hb
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian W
  set T := Finset.univ.filter (fun i : Fin r => j i ∈ S.support) with hT
  have hrad : ∀ k ∈ T.map (Fin.castLEEmb hr), (Ideal.span {t k}).IsRadical := by
    intro k hk
    obtain ⟨i0, -, rfl⟩ := Finset.mem_map.mp hk
    change (Ideal.span {t (Fin.castLE hr i0)}).IsRadical
    rw [← (hjD i0).2.2]
    exact isRadical_idealSheaf_ideal _ W
  have hSW : S.suppIdeal.ideal W = ⨅ k ∈ T.map (Fin.castLEEmb hr), Ideal.span {t k} := by
    rw [MMP.Intersection.suppIdeal_eq_finsetInf, finsetInf_ideal]
    refine le_antisymm (le_iInf₂ fun k hk => ?_) (Finset.le_inf fun E hE => ?_)
    · obtain ⟨i0, hi0, rfl⟩ := Finset.mem_map.mp hk
      exact (Finset.inf_le (Finset.mem_filter.mp hi0).2).trans (le_of_eq (hjD i0).2.2)
    · by_cases hmeet : ∃ y ∈ (W : X.Opens), y ∈ E.support
      · obtain ⟨y, hyW, hyE⟩ := hmeet
        obtain ⟨i0, rfl⟩ := exists_eq_of_mem_chart t hr j (fun i => (hjD i).2.2) hDW (hSD E hE)
          hyW hyE
        exact (iInf₂_le (Fin.castLE hr i0) (Finset.mem_map_of_mem (Fin.castLEEmb hr)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hE⟩))).trans (le_of_eq (hjD i0).2.2.symm)
      · rw [ideal_eq_top_of_disjoint _ W (fun y hy hyE => hmeet ⟨y, hy, hyE⟩)]
        exact le_top
  rw [← span_prod_eq_iInf_of_basis_D t b hb _ hrad, Finset.prod_map] at hSW
  refine ⟨W, T.card, fun k => j (T.equivFin.symm k), fun k => t (Fin.castLE hr (T.equivFin.symm k)),
    hxW, fun k => ⟨(hjD _).1, (hjD _).2.2⟩, ?_⟩
  rw [hSW]
  congr 2
  rw [← Finset.prod_coe_sort]
  exact Fintype.prod_equiv T.equivFin (fun i => t (Fin.castLEEmb hr i))
    (fun k => t (Fin.castLE hr (T.equivFin.symm k))) (fun i => by
      rw [Equiv.symm_apply_apply]
      rfl)

/-- Finitely many properties of opens, each stable under shrinking and each holding near `y`,
hold together on an affine neighbourhood of `y` inside any given neighbourhood. -/
theorem exists_affine_forall {ι : Type*} (s : Finset ι) (P : ι → X.Opens → Prop)
    (hP : ∀ i (W W' : X.Opens), W' ≤ W → P i W → P i W') {y : X}
    (hloc : ∀ i ∈ s, ∃ W : X.Opens, y ∈ W ∧ P i W) (W₀ : X.Opens) (hy₀ : y ∈ W₀) :
    ∃ W : X.affineOpens, y ∈ (W : X.Opens) ∧ (W : X.Opens) ≤ W₀ ∧ ∀ i ∈ s, P i W := by
  classical
  suffices h : ∃ W : X.Opens, y ∈ W ∧ W ≤ W₀ ∧ ∀ i ∈ s, P i W by
    obtain ⟨W, hyW, hW₀, hPW⟩ := h
    obtain ⟨U₁, hU₁, hy₁, hle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hyW
    exact ⟨⟨U₁, hU₁⟩, hy₁, hle.trans hW₀, fun i hi => hP i _ _ hle (hPW i hi)⟩
  induction s using Finset.induction_on with
  | empty => exact ⟨W₀, hy₀, le_rfl, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨W, hyW, hW₀, hPW⟩ := ih fun i hi => hloc i (Finset.mem_insert_of_mem hi)
    obtain ⟨Wa, hya, hPa⟩ := hloc a (Finset.mem_insert_self a s)
    refine ⟨W ⊓ Wa, ⟨hyW, hya⟩, inf_le_left.trans hW₀, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hP _ _ _ inf_le_right hPa
    · exact hP _ _ _ inf_le_left (hPW i hi)

end SChart

/-! ### Valuations of local equations -/

section Valuations

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- A local equation `t` of a prime divisor `E` on an affine open meeting `E` is a uniformizer
along `E`. -/
theorem valuation_germ_eq_exp_one (E : MMP.Mori.PrimeDivisor X) (W : X.affineOpens)
    (t : Γ(X, W)) (ht : E.idealSheaf.ideal W = Ideal.span {t})
    (hEW : (E.support ∩ (W : X.Opens)).Nonempty) :
    E.valuation ((X.presheaf.germ (W : X.Opens) (componentGenericPoint X E.component)
      (E.componentGenericPoint_mem_of_nonempty hEW)).hom t) = WithZero.exp 1 := by
  have hη : E.genericPoint ∈ (W : X.Opens) := E.genericPoint_mem_of_nonempty hEW
  have := E.isDiscreteValuationRing_localRing
  have hmax : IsLocalRing.maximalIdeal E.localRing =
      Ideal.span {(X.presheaf.germ (W : X.Opens) E.genericPoint hη).hom t} :=
    (MMP.Resolution.Aux.stalk_idealSheaf_genericPoint E).symm.trans
      (AlgebraicGeometry.IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span hη ht)
  have hirr : Irreducible ((X.presheaf.germ (W : X.Opens) E.genericPoint hη).hom t) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have h := E.valuation_toComponent_of_irreducible hirr
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply] at h
  exact h

/-- A local equation of a prime divisor `P` is a unit along every other prime divisor. -/
theorem valuation_germ_eq_one (P : MMP.Mori.PrimeDivisor X) (W : X.affineOpens)
    (t : Γ(X, W)) (ht : P.idealSheaf.ideal W = Ideal.span {t}) (E : MMP.Mori.PrimeDivisor X)
    (hEW : (E.support ∩ (W : X.Opens)).Nonempty) (hne : E ≠ P) :
    E.valuation ((X.presheaf.germ (W : X.Opens) (componentGenericPoint X E.component)
      (E.componentGenericPoint_mem_of_nonempty hEW)).hom t) = 1 := by
  have hη : E.genericPoint ∈ (W : X.Opens) := E.genericPoint_mem_of_nonempty hEW
  have hbo : E.genericPoint ∈ X.basicOpen t := by
    by_contra h
    exact hne (eq_of_genericPoint_mem_support (mem_support_of_ideal_eq_span ht hη h))
  have hunit : IsUnit ((X.presheaf.germ (W : X.Opens) E.genericPoint hη).hom t) :=
    (X.mem_basicOpen t E.genericPoint hη).mp hbo
  have h := E.valuation_toComponent_of_isUnit hunit
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply] at h
  exact h

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The generic point of an irreducible component is maximal for generization. -/
theorem specializes_componentGenericPoint_eq {Z : irreducibleComponents X} {y : X}
    (h : y ⤳ componentGenericPoint X Z) : y = componentGenericPoint X Z := by
  have hZ := isGenericPoint_componentGenericPoint X Z
  have hsub : (Z : Set X) ⊆ closure {y} := by
    rw [← hZ.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp h))
      isClosed_closure
  have heq : closure {y} = (Z : Set X) :=
    (Z.2.2 (isIrreducible_singleton.closure) hsub).antisymm hsub
  exact (hZ.eq (by rw [IsGenericPoint, heq])).symm

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A local equation of a prime divisor is a unit at the generic point of every irreducible
component meeting the open. -/
theorem isUnit_germ_componentGenericPoint (P : MMP.Mori.PrimeDivisor X) (W : X.affineOpens)
    (t : Γ(X, W)) (ht : P.idealSheaf.ideal W = Ideal.span {t}) (Z : irreducibleComponents X)
    (hZ : componentGenericPoint X Z ∈ (W : X.Opens)) :
    IsUnit ((X.presheaf.germ (W : X.Opens) (componentGenericPoint X Z) hZ).hom t) := by
  refine (X.mem_basicOpen t _ hZ).mp ?_
  by_contra h
  have hmem : componentGenericPoint X Z ∈ P.support := mem_support_of_ideal_eq_span ht hZ h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
  have hsp : P.genericPoint ⤳ componentGenericPoint X Z := specializes_iff_mem_closure.mpr hmem
  have heq := specializes_componentGenericPoint_eq hsp
  have h1 := MMP.Mori.PrimeDivisor.coheight_genericPoint P
  rw [heq, Order.coheight_eq_zero.mpr fun y hy => ?_] at h1
  · exact absurd h1 (by decide)
  · exact (specializes_componentGenericPoint_eq (Z := Z) hy) ▸ le_rfl

open Classical in
/-- The valuation of a monomial in local equations of distinct prime divisors. -/
theorem valuation_germ_prod_pow {r : ℕ} (W : X.affineOpens) (τ : Fin r → Γ(X, W))
    (j : Fin r → MMP.Mori.PrimeDivisor X)
    (hτ : ∀ k, (j k).idealSheaf.ideal W = Ideal.span {τ k}) (b : Fin r → ℕ)
    (E : MMP.Mori.PrimeDivisor X) (hEW : (E.support ∩ (W : X.Opens)).Nonempty) :
    E.valuation ((X.presheaf.germ (W : X.Opens) (componentGenericPoint X E.component)
      (E.componentGenericPoint_mem_of_nonempty hEW)).hom (∏ k, τ k ^ b k)) =
      ∏ k, (if E = j k then WithZero.exp (b k : ℤ) else 1) := by
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_pow, map_pow]
  split_ifs with h
  · subst h
    rw [valuation_germ_eq_exp_one _ W (τ k) (hτ k) hEW, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_one]
  · rw [valuation_germ_eq_one (j k) W (τ k) (hτ k) E hEW h, one_pow]

end Valuations

/-! ### Local generators of `𝒪_X(-M)` -/

section Generators

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (D M : Divisor X)

/-- The restriction of a rational function to an open. -/
noncomputable abbrev ratRes (W : X.Opens) (φ : RationalFunctions X) :
    ToType ((rationalFunctionsPresheaf X).obj (op W)) :=
  (rationalFunctionsPresheaf X).map (homOfLE le_top).op ((rationalFunctionsPresheafTopEquiv
      X).symm φ)

/-- **Local generators of `𝒪_X(-M)`.** If `φ₀` is a local equation of `M` on `W`, then `φ₀` is a
function `g₀` on `W ∩ U'`, it is a section of `𝒪_X(-M)` over `W`, and it generates `𝒪_X(-M)` on
every open of `W`. -/
theorem exists_generator {W : X.Opens} {φ₀ : (RationalFunctions X)ˣ}
    (hφ₀ : M.IsLocalEquation W φ₀) :
    ∃ g₀ : Γ(X, W ⊓ cU' D M),
      (toRationalFunctionsPresheaf X).app (op (W ⊓ cU' D M)) g₀ = ratRes (W ⊓ cU' D M) φ₀ ∧
      DivCond (D := D) (M := M) W g₀ ∧
      ∀ (W₃ : X.Opens) (h₃ : W₃ ≤ W) (g : Γ(X, W₃ ⊓ cU' D M)), DivCond (D := D) (M := M) W₃ g →
        ∃ h : Γ(X, W₃), g = X.presheaf.map (homOfLE inf_le_left).op h *
          X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g₀ := by
  have hord : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ (W ⊓ cU' D M : X.Opens)).Nonempty →
      E.ord φ₀ = 0 := by
    intro E hE
    rw [← hφ₀ E (hE.mono (Set.inter_subset_inter_right _ inf_le_left))]
    exact coeff_eq_zero_of_meets (W := W ⊓ cU' D M) (fun x (hx : x ∈ W ⊓ cU' D M) hxM =>
      (hx.2 : x ∉ ((D.supp ⊔ M.supp : TopologicalSpace.Closeds X) : Set X)) (Or.inr hxM)) hE
  have hdiv : (0 : Divisor X).IsDivisorialSection (W ⊓ cU' D M) (ratRes (W ⊓ cU' D M) φ₀) := by
    intro E hE
    refine Or.inr ?_
    have h1 := E.valuation_component φ₀
    rw [hord E hE] at h1
    rw [DivisorWithCoeffs.coeff_zero, neg_zero]
    exact h1.ge
  obtain ⟨g₀, hg₀⟩ := hdiv.exists_eq
  refine ⟨g₀, hg₀, ⟨ratRes W φ₀, fun E hE => ?_, ?_⟩, ?_⟩
  · refine Or.inr ?_
    have h1 := E.valuation_component φ₀
    rw [← hφ₀ E hE] at h1
    rw [DivisorWithCoeffs.coeff_neg, neg_neg]
    exact h1.ge
  · rw [hg₀]
    rfl
  · rintro W₃ h₃ g ⟨a, ha, hag⟩
    have hdiv' : (0 : Divisor X).IsDivisorialSection W₃
        (a * ratRes W₃ ↑φ₀⁻¹) := by
      intro E hE
      have h1 := E.valuation_component φ₀⁻¹
      rw [MMP.Mori.PrimeDivisor.ord_inv,
        ← hφ₀ E (hE.mono (Set.inter_subset_inter_right _ h₃))] at h1
      have h2 : E.OrdGE (-M.coeff E) (ratRes W₃ ↑φ₀⁻¹ ⟨E.component,
          E.componentGenericPoint_mem_of_nonempty hE⟩) := Or.inr h1.ge
      have h3 := (ha E hE).mul h2
      rw [DivisorWithCoeffs.coeff_neg, neg_neg, add_neg_cancel] at h3
      rw [DivisorWithCoeffs.coeff_zero, neg_zero]
      exact h3
    obtain ⟨h, hh⟩ := hdiv'.exists_eq
    refine ⟨h, toRationalFunctionsPresheaf_app_injective _ ?_⟩
    have e1 : (toRationalFunctionsPresheaf X).app (op (W₃ ⊓ cU' D M))
        (X.presheaf.map (homOfLE inf_le_left).op h) = (rationalFunctionsPresheaf X).map
          (homOfLE inf_le_left).op ((toRationalFunctionsPresheaf X).app (op W₃) h) :=
      congrArg (fun φ => φ.hom h) ((toRationalFunctionsPresheaf X).naturality
        (homOfLE (inf_le_left : W₃ ⊓ cU' D M ≤ W₃)).op)
    have e2 : (toRationalFunctionsPresheaf X).app (op (W₃ ⊓ cU' D M))
        (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g₀) =
        (rationalFunctionsPresheaf X).map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op
          ((toRationalFunctionsPresheaf X).app (op (W ⊓ cU' D M)) g₀) :=
      congrArg (fun φ => φ.hom g₀) ((toRationalFunctionsPresheaf X).naturality
        (homOfLE (inf_le_inf_right (cU' D M) h₃)).op)
    rw [← hag, map_mul, e1, e2, hh, hg₀]
    funext Z
    refine Eq.symm ?_
    change a ⟨Z.1, Z.2.1⟩ * (↑φ₀⁻¹ : RationalFunctions X) Z.1 * (φ₀ : RationalFunctions X) Z.1 =
      a ⟨Z.1, Z.2.1⟩
    rw [mul_assoc, ← Pi.mul_apply (↑φ₀⁻¹ : RationalFunctions X), Units.inv_mul, Pi.one_apply,
      mul_one]

/-- `∏ₖ exp(aₖ) = exp(∑ₖ aₖ)` in `ℤᵐ⁰`. -/
theorem prod_exp_eq_exp_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ) :
    ∏ k ∈ s, WithZero.exp (a k) = WithZero.exp (∑ k ∈ s, a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [WithZero.exp_zero]
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, WithZero.exp_add]

open Classical in
/-- **A unit from a divisor computation.** If `v_E(φ) = ∑ₖ [E = jₖ] bₖ` for every prime divisor
`E` meeting `W`, then `φ = v · ∏ τₖ^{bₖ}` on `W` with `v` a unit. -/
theorem exists_isUnit_mul_prod_pow {r : ℕ} (W : X.affineOpens) (τ : Fin r → Γ(X, W))
    (j : Fin r → MMP.Mori.PrimeDivisor X)
    (hτ : ∀ k, (j k).idealSheaf.ideal W = Ideal.span {τ k}) (b : Fin r → ℕ)
    (φ : (RationalFunctions X)ˣ)
    (hord : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ (W : X.Opens)).Nonempty →
      E.ord φ = ∑ k, if E = j k then (b k : ℤ) else 0) :
    ∃ v : Γ(X, W), IsUnit v ∧
      (toRationalFunctionsPresheaf X).app (op (W : X.Opens)) (v * ∏ k, τ k ^ b k) =
        ratRes (W : X.Opens) φ := by
  set βR := (toRationalFunctionsPresheaf X).app (op (W : X.Opens)) (∏ k, τ k ^ b k)
  have hβu : IsUnit βR := by
    refine Pi.isUnit_iff.mpr fun Z => ?_
    change IsUnit ((X.presheaf.germ (W : X.Opens) (componentGenericPoint X Z.1) Z.2).hom
      (∏ k, τ k ^ b k))
    rw [map_prod]
    exact Finset.prod_induction _ IsUnit (fun a c ha hc => ha.mul hc) isUnit_one fun k _ => by
      rw [map_pow]
      exact (isUnit_germ_componentGenericPoint (j k) W (τ k) (hτ k) Z.1 Z.2).pow _
  set βi := (↑(hβu.unit⁻¹) : ToType ((rationalFunctionsPresheaf X).obj (op (W : X.Opens))))
  have hβi : βi * βR = 1 := by
    rw [← hβu.unit_spec]
    exact Units.inv_mul _
  have hval : ∀ (E : MMP.Mori.PrimeDivisor X) (hE : (E.support ∩ (W : X.Opens)).Nonempty),
      E.valuation (βR ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) =
        WithZero.exp (E.ord φ) := by
    intro E hE
    change E.valuation ((X.presheaf.germ (W : X.Opens) _ _).hom (∏ k, τ k ^ b k)) = _
    rw [valuation_germ_prod_pow W τ j hτ b E hE, hord E hE, ← prod_exp_eq_exp_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp [WithZero.exp_zero]
  have hvalβi : ∀ (E : MMP.Mori.PrimeDivisor X) (hE : (E.support ∩ (W : X.Opens)).Nonempty),
      E.valuation (βi ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) *
        WithZero.exp (E.ord φ) = 1 := by
    intro E hE
    rw [← hval E hE, ← map_mul]
    change E.valuation ((βi * βR) ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) = 1
    rw [hβi]
    exact map_one _
  have hdivv : (0 : Divisor X).IsDivisorialSection W (ratRes (W : X.Opens) φ * βi) := by
    intro E hE
    refine Or.inr (le_of_eq ?_)
    rw [DivisorWithCoeffs.coeff_zero, neg_zero, WithZero.exp_zero]
    change 1 = E.valuation ((φ : RationalFunctions X) E.component * βi ⟨E.component, _⟩)
    rw [map_mul, E.valuation_component φ, mul_comm, hvalβi E hE]
  have hdivw : (0 : Divisor X).IsDivisorialSection W (βR * ratRes (W : X.Opens) ↑φ⁻¹) := by
    intro E hE
    refine Or.inr (le_of_eq ?_)
    rw [DivisorWithCoeffs.coeff_zero, neg_zero, WithZero.exp_zero]
    change 1 = E.valuation (βR ⟨E.component, _⟩ * (↑φ⁻¹ : RationalFunctions X) E.component)
    rw [map_mul, hval E hE, E.valuation_component φ⁻¹, MMP.Mori.PrimeDivisor.ord_inv,
      ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  obtain ⟨v, hv⟩ := hdivv.exists_eq
  obtain ⟨w, hw⟩ := hdivw.exists_eq
  have hφφ : ratRes (W : X.Opens) φ * ratRes (W : X.Opens) ↑φ⁻¹ = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine ⟨v, IsUnit.of_mul_eq_one w (toRationalFunctionsPresheaf_app_injective _ ?_), ?_⟩
  · rw [map_mul, map_one, hv, hw]
    calc ratRes (W : X.Opens) φ * βi * (βR * ratRes (W : X.Opens) ↑φ⁻¹) =
        (ratRes (W : X.Opens) φ * ratRes (W : X.Opens) ↑φ⁻¹) * (βi * βR) := by ring
      _ = 1 := by rw [hφφ, hβi, one_mul]
  · rw [map_mul, hv, mul_assoc, hβi, mul_one]

end Generators

/-- **A factorization of a local generator near a point.** Near every point `y` there are an
affine open `W₂`, local equations `τₖ` on `W₂` of the components `jₖ` of `D` through `W₂`, with
`D = V(∏ τₖ)` on `W₂`, a unit `v` on `W₂` and a generator `g₀` of `𝒪_X(-M)` on every open of `W₂`
with `g₀^N = u · v · ∏ τₖ^{Bn(jₖ)}` on `W₂ ∩ U'`. -/
theorem exists_generator_factorization (n : ℕ) {X T : Scheme.{u}} (f : X ⟶ T)
    [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X)
    (hD : D.IsRelativeSNC n f) (M : Divisor X) (uu : Γ(X, cU' D M)) [CompactSpace X]
    (hMC : M.IsCartier) (Bn : Divisor X) (N : ℕ) (ψ : (RationalFunctions X)ˣ)
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (hu : (toRationalFunctionsPresheaf X).app (op (cU' D M)) uu = ratRes (cU' D M) ψ)
    (hBn : ∀ E, 0 ≤ Bn E) (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support) (y : X) :
    ∃ (W₂ : X.affineOpens) (_ : y ∈ (W₂ : X.Opens)) (r : ℕ) (τ : Fin r → Γ(X, W₂))
      (j : Fin r → MMP.Mori.PrimeDivisor X) (v : Γ(X, W₂)) (g₀ : Γ(X, (W₂ : X.Opens) ⊓ cU' D M)),
      Function.Injective j ∧ (∀ k, j k ∈ D.support) ∧
      (∀ k, (j k).idealSheaf.ideal W₂ = Ideal.span {τ k}) ∧
      D.suppIdeal.ideal W₂ = Ideal.span {∏ k, τ k} ∧ IsUnit v ∧
      DivCond (D := D) (M := M) (W₂ : X.Opens) g₀ ∧
      (∀ (W₃ : X.Opens) (h₃ : W₃ ≤ W₂) (g : Γ(X, W₃ ⊓ cU' D M)), DivCond (D := D) (M := M) W₃ g →
        ∃ h : Γ(X, W₃), g = X.presheaf.map (homOfLE inf_le_left).op h *
          X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g₀) ∧
      g₀ ^ N = X.presheaf.map (homOfLE inf_le_right).op uu *
        X.presheaf.map (homOfLE inf_le_left).op (v * ∏ k, τ k ^ (Bn (j k)).toNat) := by
  classical
  obtain ⟨W, hyW, φ₀, hφ₀⟩ := hMC y
  obtain ⟨Wc, Vb, e, t, hyc, -, r, hr, j, hj, hjD, hDW⟩ := hD.2 y
  obtain ⟨U₂, hU₂, hy₂, hle₂⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show y ∈ W ⊓ (Wc : X.Opens) from ⟨hyW, hyc⟩)
  let W₂ : X.affineOpens := ⟨U₂, hU₂⟩
  have k₁ : (W₂ : X.Opens) ≤ W := hle₂.trans inf_le_left
  have kc : (W₂ : X.Opens) ≤ Wc := hle₂.trans inf_le_right
  let τ : Fin r → Γ(X, W₂) := fun k => X.presheaf.map (homOfLE kc).op (t (Fin.castLE hr k))
  have hτ : ∀ k, (j k).idealSheaf.ideal W₂ = Ideal.span {τ k} := fun k => by
    rw [← (j k).idealSheaf.map_ideal kc, (hjD k).2.2, Ideal.map_span, Set.image_singleton]
    rfl
  have hDW₂ : D.suppIdeal.ideal W₂ = Ideal.span {∏ k, τ k} := by
    rw [← D.suppIdeal.map_ideal kc, hDW, Ideal.map_span, Set.image_singleton, map_prod]
    rfl
  let b : Fin r → ℕ := fun k => (Bn (j k)).toNat
  have hord : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ (W₂ : X.Opens)).Nonempty →
      E.ord (φ₀ ^ N * ψ⁻¹) = ∑ k, if E = j k then (b k : ℤ) else 0 := by
    intro E hE
    have hBnE : Bn E = ∑ k, if E = j k then (b k : ℤ) else 0 := by
      by_cases hEj : ∃ k, E = j k
      · obtain ⟨k0, rfl⟩ := hEj
        rw [Finset.sum_eq_single k0 (fun k _ hk => ite_eq_right (fun h => hk (hj h).symm))
          (by simp), ite_eq_left rfl]
        exact (Int.toNat_of_nonneg (hBn _)).symm
      · rw [Finset.sum_eq_zero (fun k _ => ite_eq_right fun h => hEj ⟨k, h⟩)]
        by_contra hne
        obtain ⟨x, hxE, hxW⟩ := hE
        obtain ⟨k, hk⟩ := exists_eq_of_mem_chart τ le_rfl j hτ hDW₂ (hBD E hne)
          hxW hxE
        exact hEj ⟨k, hk.symm⟩
    have h1 := congrArg (fun F : Divisor X => F E) hψ
    simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at h1
    rw [MMP.Mori.PrimeDivisor.ord_mul, MMP.Mori.PrimeDivisor.ord_pow,
      MMP.Mori.PrimeDivisor.ord_inv, ← hφ₀ E (hE.mono (Set.inter_subset_inter_right _ k₁)),
      ← MMP.Mori.coeff_principalDivisor, ← hBnE, nsmul_eq_mul]
    change (N : ℤ) * M E + -(MMP.Mori.principalDivisor ψ) E = Bn E
    linarith
  obtain ⟨v, hvu, hvrel⟩ := exists_isUnit_mul_prod_pow W₂ τ j hτ b (φ₀ ^ N * ψ⁻¹) hord
  obtain ⟨g₀, hg₀rat, hg₀div, hg₀gen⟩ := exists_generator D M (hφ₀.mono k₁)
  have hX : g₀ ^ N = X.presheaf.map (homOfLE inf_le_right).op uu *
      X.presheaf.map (homOfLE inf_le_left).op (v * ∏ k, τ k ^ b k) := by
    apply toRationalFunctionsPresheaf_app_injective
    have n1 := congrArg (fun φ => φ.hom uu) ((toRationalFunctionsPresheaf X).naturality
      (homOfLE (inf_le_right : (W₂ : X.Opens) ⊓ cU' D M ≤ cU' D M)).op)
    have n2 := congrArg (fun φ => φ.hom (v * ∏ k, τ k ^ b k))
      ((toRationalFunctionsPresheaf X).naturality
        (homOfLE (inf_le_left : (W₂ : X.Opens) ⊓ cU' D M ≤ W₂)).op)
    rw [map_pow, map_mul, hg₀rat]
    erw [n1, n2]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [hu, hvrel]
    funext Z
    change ((φ₀ : RationalFunctions X) Z.1) ^ N =
      (ψ : RationalFunctions X) Z.1 * (↑(φ₀ ^ N * ψ⁻¹) : RationalFunctions X) Z.1
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Pi.mul_apply, Pi.pow_apply, mul_left_comm,
      ← Pi.mul_apply (↑ψ : RationalFunctions X), Units.mul_inv, Pi.one_apply, mul_one]
  exact ⟨W₂, hy₂, r, τ, j, v, g₀, hj, fun k => (hjD k).1, hτ, hDW₂, hvu, hg₀div, hg₀gen, hX⟩

/-! ### `∇` preserves `C^•` -/

section Stability

variable (n : ℕ) {X T : Scheme.{u}} (f : X ⟶ T) [SmoothOfRelativeDimension n f]
  [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) (hD : D.IsRelativeSNC n f) (S M : Divisor X)
  (uu cc : Γ(X, cU' D M))

/-- Local data for `∇` near a point: a generator `g₀` of `𝒪_X(-M)` on `W₂` (on every smaller
open) and a logarithmic one-form `ξ₀` with `∇ g₀ = g₀ ξ₀`. -/
def GenData (W₂ : X.Opens) (g₀ : Γ(X, W₂ ⊓ cU' D M))
    (ξ₀ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₂))) : Prop :=
  DivCond (D := D) (M := M) W₂ g₀ ∧ ξ₀ ∈ relativeLogForms n f D hD ⊤ 1 W₂ ∧
  (∀ (W₃ : X.Opens) (h₃ : W₃ ≤ W₂) (g : Γ(X, W₃ ⊓ cU' D M)), DivCond (D := D) (M := M) W₃ g →
    ∃ h : Γ(X, W₃), g = X.presheaf.map (homOfLE inf_le_left).op h *
      X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h₃)).op g₀) ∧
  δ ((cU D).ι ≫ f) (OO D M W₂) ((cU D).ι.app _ g₀) -
      (TB ((cU D).ι ≫ f)).incl 1 (θW f D M uu cc W₂) *
        sm ((cU D).ι ≫ f) (OO D M W₂) ((cU D).ι.app _ g₀) =
    sm ((cU D).ι ≫ f) (OO D M W₂) ((cU D).ι.app _ g₀) * (TB ((cU D).ι ≫ f)).incl 1
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.map
        (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op ξ₀)

/-- The form `h ξ ∧ η + dh ∧ η + h dη`, which is `∇(h g₀ η) / g₀` when `∇ g₀ = g₀ ξ`. -/
noncomputable def zetaForm (p : ℕ) (W₃ : X.Opens) (h : Γ(X, W₃))
    (ξ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₃)))
    (η : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₃))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece ((p + 1 : ℕ) : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₃)) :=
  asStr (((cU D).ι.app W₃).hom h) • wedgeOne _ p ξ η +
    wedgeOne _ p (dF f D _ (((cU D).ι.app W₃).hom h)) η +
    asStr (((cU D).ι.app W₃).hom h) •
      asPiece (((Scheme.Hom.deRhamComplex ((cU D).ι ≫ f)).d p (p + 1)).val.app _ η)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- If `ξ` is a logarithmic one-form and `η` lies in `Ω^p_X(log D)(-S)`, then
`zetaForm f D p W₃ h ξ η` lies in `Ω^{p+1}_X(log D)(-S)`. -/
theorem zetaForm_mem (hchart : ∀ x : X, ∃ (Wc : X.affineOpens) (r : ℕ)
      (j : Fin r → MMP.Mori.PrimeDivisor X) (t : Fin r → Γ(X, Wc)), x ∈ (Wc : X.Opens) ∧
        (∀ i, j i ∈ D.support ∧ (j i).idealSheaf.ideal Wc = Ideal.span {t i}) ∧
        S.suppIdeal.ideal Wc = Ideal.span {∏ i, t i})
    (p : ℕ) (W₃ : X.Opens) (h : Γ(X, W₃)) (ξ η)
    (hξ : ξ ∈ relativeLogForms n f D hD ⊤ 1 W₃)
    (hη : η ∈ relativeLogForms n f D hD S.suppIdeal p W₃) :
    zetaForm f D p W₃ h ξ η ∈ relativeLogForms n f D hD S.suppIdeal ((p + 1 : ℕ) : ℤ) W₃ := by
  unfold zetaForm
  refine G1.add_mem_relativeLogForms n f D hD _ _ (G1.add_mem_relativeLogForms n f D hD _ _
    (G1.smul_mem_relativeLogForms n f D hD _ _ h
      (B1.wedgeOne_mem_relativeLogForms f D n hD _ p W₃ ξ η hξ hη))
    (B1.wedgeOne_mem_relativeLogForms f D n hD _ p W₃ _ η
      (B1.δ_mem_relativeLogForms f D n hD W₃ h) hη))
    (G1.smul_mem_relativeLogForms n f D hD _ _ h
      (B1.deRham_mem_relativeLogForms_of_charts f D n hD _ hchart p W₃ η hη))

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- In the total ring of forms over `U ∩ W₃ ∩ U'`, the restriction of `zetaForm f D p W₃ h ξ η` is
`h ξ ∧ η + dh ∧ η + h dη`. -/
theorem incl_map_zetaForm (p : ℕ) (W₃ : X.Opens) (h : Γ(X, W₃)) (ξ η) :
    (TB ((cU D).ι ≫ f)).incl ((p + 1 : ℕ) : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
          ((p + 1 : ℕ) : ℤ)).val.map
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left : W₃ ⊓ cU' D M ≤ W₃))).op
          (zetaForm f D p W₃ h ξ η)) =
      let ψ := (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left : W₃ ⊓ cU' D M ≤ W₃))).op
      let h' := (cU D).toScheme.presheaf.map ψ (((cU D).ι.app W₃).hom h)
      let z := (TB ((cU D).ι ≫ f)).incl (p : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map ψ η)
      sm ((cU D).ι ≫ f) (OO D M W₃) h' * ((TB ((cU D).ι ≫ f)).incl 1
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.map ψ ξ) *
          z) +
        δ ((cU D).ι ≫ f) (OO D M W₃) h' * z + sm ((cU D).ι ≫ f) (OO D M W₃) h' *
          Δ ((cU D).ι ≫ f) (OO D M W₃) p z := by
  dsimp only
  unfold zetaForm
  rw [map_add, map_add]
  refine ((TB ((cU D).ι ≫ f)).incl_add _ _ _).trans ?_
  refine congrArg₂ (· + ·) (((TB ((cU D).ι ≫ f)).incl_add _ _ _).trans
    (congrArg₂ (· + ·) ?_ ?_)) ?_
  · exact (incl_map_smul _ _ _ _).trans (congrArg _ (incl_map_wedgeOne _ _ _ _))
  · exact (incl_map_wedgeOne _ _ _ _).trans
      (congrArg (· * _) (congrArg ((TB ((cU D).ι ≫ f)).incl 1) (dF_restrict f D _ _)))
  · exact (incl_map_smul _ _ _ _).trans (congrArg _
      ((congrArg ((TB ((cU D).ι ≫ f)).incl _) (deRham_map _ _ _).symm).trans (Δ_incl _ _).symm))

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Finitely many `I`-twisted logarithmic forms are, near any point, sums of products
`b · dc₁ ∧ ⋯ ∧ dc_p` on a common affine neighbourhood. -/
theorem exists_affine_monSet (I : X.IdealSheafData) {p : ℕ} {W₁ : X.Opens} {m : ℕ}
    (η : Fin m → ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (p : ℤ)).val.obj (op ((cU D).ι ⁻¹ᵁ W₁)))
    (hη : ∀ i, η i ∈ relativeLogForms n f D hD I p W₁) {y : X} (hy₁ : y ∈ W₁)
    (W₀ : X.Opens) (hy₀ : y ∈ W₀) :
    ∃ W₃ : X.affineOpens, y ∈ (W₃ : X.Opens) ∧ (W₃ : X.Opens) ≤ W₀ ∧
      ∀ i ∈ (Finset.univ : Finset (Fin m)), ∃ h : (W₃ : X.Opens) ≤ W₁,
        (TB ((cU D).ι ≫ f)).incl (p : ℤ)
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
            (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans h))).op (η i)) ∈
          monSet ((cU D).ι ≫ f) (OO D M W₃) := by
  refine exists_affine_forall _ (fun i (W' : X.Opens) => ∃ h : W' ≤ W₁,
      (TB ((cU D).ι ≫ f)).incl (p : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans h))).op (η i)) ∈
        monSet ((cU D).ι ≫ f) (OO D M W')) ?_ ?_ W₀ hy₀
  · rintro i W' W'' hle ⟨h, hm⟩
    refine ⟨hle.trans h, ?_⟩
    have e := (incl_map f D (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
        (inf_le_inf_right (cU' D M) hle))).op (p : ℤ) _).symm.trans
      (congrArg ((TB ((cU D).ι ≫ f)).incl (p : ℤ))
        (piece_map_map _ (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans h))).op
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_inf_right (cU' D M) hle))).op
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans (hle.trans h)))).op
          (η i)))
    exact e ▸ totalRestrict_mem_monSet _ hm
  · intro i _
    obtain ⟨W', h', hy', hm⟩ := NearMon.of_relativeLogForms n f D hD M I (hη i) hy₁
    refine ⟨W', hy', h', ?_⟩
    have e := (incl_map f D (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
        (inf_le_inf_right (cU' D M) h'))).op (p : ℤ) _).symm.trans
      (congrArg ((TB ((cU D).ι ≫ f)).incl (p : ℤ))
        (piece_map_map _ (homOfLE (Scheme.Hom.preimage_mono (cU D).ι inf_le_left)).op
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_inf_right (cU' D M) h'))).op
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans h'))).op (η i)))
    exact e ▸ hm

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- The identity `∇ g₀ = g₀ ξ₀` restricts to every smaller open. -/
theorem genData_nab_restrict {W₂ W₃ : X.Opens} (k₂ : W₃ ≤ W₂) {g₀ : Γ(X, W₂ ⊓ cU' D M)}
    {ξ₀ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₂))}
    (hG₄ : δ ((cU D).ι ≫ f) (OO D M W₂) ((cU D).ι.app _ g₀) -
      (TB ((cU D).ι ≫ f)).incl 1 (θW f D M uu cc W₂) *
        sm ((cU D).ι ≫ f) (OO D M W₂) ((cU D).ι.app _ g₀) =
      sm ((cU D).ι ≫ f) (OO D M W₂) ((cU D).ι.app _ g₀) * (TB ((cU D).ι ≫ f)).incl 1
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.map
          (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op ξ₀)) :
    δ ((cU D).ι ≫ f) (OO D M W₃) ((cU D).ι.app _
        (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀)) -
      (TB ((cU D).ι ≫ f)).incl 1 (θW f D M uu cc W₃) * sm ((cU D).ι ≫ f) (OO D M W₃)
        ((cU D).ι.app _ (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀)) =
      sm ((cU D).ι ≫ f) (OO D M W₃) ((cU D).ι.app _
          (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀)) *
        (TB ((cU D).ι ≫ f)).incl 1
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.map
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
            (inf_le_left : W₃ ⊓ cU' D M ≤ W₃))).op (G1.rs f D 1 k₂ ξ₀)) := by
  set g₀' := X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀
  set ψ₃ := (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left : W₃ ⊓ cU' D M ≤ W₃))).op
  set φ : op (OO D M W₂) ⟶ op (OO D M W₃) :=
    (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_inf_right (cU' D M) k₂))).op
  have ea : (cU D).toScheme.presheaf.map φ (((cU D).ι.app (W₂ ⊓ cU' D M)).hom g₀) =
      ((cU D).ι.app ((W₃ : X.Opens) ⊓ cU' D M)).hom g₀' :=
    G1.app_restrict (inf_le_inf_right (cU' D M) k₂) g₀
  have e1 := (totalRestrict_δ (g := (cU D).ι ≫ f) φ (((cU D).ι.app (W₂ ⊓ cU' D M)).hom g₀)).trans
    (congrArg _ ea)
  have e2 := ((TB ((cU D).ι ≫ f)).totalRestrict_incl φ 1 (θW f D M uu cc W₂)).trans
    (congrArg ((TB ((cU D).ι ≫ f)).incl 1) (θW_restrict f D M uu cc k₂))
  have e3 := (totalRestrict_sm (g := (cU D).ι ≫ f) φ (((cU D).ι.app (W₂ ⊓ cU' D M)).hom g₀)).trans
    (congrArg _ ea)
  have e4 := ((TB ((cU D).ι ≫ f)).totalRestrict_incl φ 1 _).trans
    (congrArg ((TB ((cU D).ι ≫ f)).incl 1)
      ((piece_map_map _ (homOfLE (Scheme.Hom.preimage_mono (cU D).ι inf_le_left)).op φ
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans k₂))).op ξ₀).trans
      (piece_map_map _ ((Opens.map (cU D).ι.base).map (homOfLE k₂)).op ψ₃
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans k₂))).op ξ₀).symm))
  have h := congrArg ((TB ((cU D).ι ≫ f)).totalRestrictRingHom φ) hG₄
  rw [map_sub, map_mul, map_mul] at h
  simp only [(TB ((cU D).ι ≫ f)).totalRestrictRingHom_apply] at h
  rw [e1, e2, e3, e4] at h
  exact h

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Restricting a form from `W₁` to `W₃` and then to `W₃ ∩ U'` is restricting it directly. -/
theorem rs_map_incl_eq (p : ℕ) {W₁ W₃ : X.Opens} (k₁ : W₃ ≤ W₁) (hk : W₃ ≤ W₁)
    (η : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₁))) :
    (TB ((cU D).ι ≫ f)).incl (p : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left : W₃ ⊓ cU' D M ≤ W₃))).op
        (G1.rs f D p k₁ η)) =
      (TB ((cU D).ι ≫ f)).incl (p : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans hk))).op η) :=
  congrArg ((TB ((cU D).ι ≫ f)).incl (p : ℤ))
    (piece_map_map ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      (p : ℤ)).val ((Opens.map (cU D).ι.base).map (homOfLE k₁)).op
      (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left : W₃ ⊓ cU' D M ≤ W₃))).op
      (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans hk))).op η)

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- One summand of `∇ω` for `ω = ∑ gᵢ ηᵢ`, with `gᵢ = hᵢ g₀` and `∇ g₀ = g₀ ξ₀`. -/
theorem nab_summand_eq (p : ℕ) {W₁ W₂ W₃ : X.Opens} (k₁ : W₃ ≤ W₁) (k₂ : W₃ ≤ W₂)
    (g : Γ(X, W₁ ⊓ cU' D M)) (hh : Γ(X, W₃)) (g₀ : Γ(X, W₂ ⊓ cU' D M))
    (ξ₀ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₂)))
    (η : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((cU D).ι ⁻¹ᵁ W₁)))
    (hhe : X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₁)).op g =
      X.presheaf.map (homOfLE inf_le_left).op hh *
        X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀)
    (hk : W₃ ≤ W₁)
    (hz : (TB ((cU D).ι ≫ f)).incl (p : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans hk))).op η) ∈
        monSet ((cU D).ι ≫ f) (OO D M W₃))
    (hξ : δ ((cU D).ι ≫ f) (OO D M W₃) ((cU D).ι.app _
        (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀)) -
      (TB ((cU D).ι ≫ f)).incl 1 (θW f D M uu cc W₃) * sm ((cU D).ι ≫ f) (OO D M W₃)
        ((cU D).ι.app _ (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀)) =
      sm ((cU D).ι ≫ f) (OO D M W₃) ((cU D).ι.app _
          (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀)) *
        (TB ((cU D).ι ≫ f)).incl 1
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.map
          (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
            (inf_le_left : W₃ ⊓ cU' D M ≤ W₃))).op (G1.rs f D 1 k₂ ξ₀))) :
    twT ((cU D).ι ≫ f) (OO D M W₃) p ((TB ((cU D).ι ≫ f)).incl 1 (θW f D M uu cc W₃))
        ((TB ((cU D).ι ≫ f)).structureMap (op (OO D M W₃))
            (((cU D).ι.app (W₃ ⊓ cU' D M)).hom
              (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₁)).op g)) *
          (TB ((cU D).ι ≫ f)).incl (p : ℤ)
            (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece (p : ℤ)).val.map
              (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans k₁))).op η)) =
      (TB ((cU D).ι ≫ f)).structureMap (op (OO D M W₃))
          (((cU D).ι.app (W₃ ⊓ cU' D M)).hom
            (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀)) *
        (TB ((cU D).ι ≫ f)).incl ((p + 1 : ℕ) : ℤ)
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
            ((p + 1 : ℕ) : ℤ)).val.map
            (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left : W₃ ⊓ cU' D M ≤ W₃))).op
            (zetaForm f D p W₃ hh (G1.rs f D 1 k₂ ξ₀) (G1.rs f D p k₁ η))) := by
  have hmul : ((cU D).ι.app (W₃ ⊓ cU' D M)).hom
      (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₁)).op g) =
      ((cU D).ι.app (W₃ ⊓ cU' D M)).hom (X.presheaf.map (homOfLE inf_le_left).op hh) *
      ((cU D).ι.app (W₃ ⊓ cU' D M)).hom
        (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀) := by
    rw [hhe, map_mul]
  have hzeta := incl_map_zetaForm f D M p W₃ hh (G1.rs f D 1 k₂ ξ₀) (G1.rs f D p k₁ η)
  have hh' : (cU D).toScheme.presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left : W₃ ⊓ cU' D M ≤ W₃))).op
      (((cU D).ι.app W₃).hom hh) =
      ((cU D).ι.app (W₃ ⊓ cU' D M)).hom (X.presheaf.map (homOfLE inf_le_left).op hh) :=
    G1.app_restrict inf_le_left hh
  have hz' := rs_map_incl_eq f D M p k₁ hk η
  exact twT_summand p _ _ _ _ _ _ _ hz hξ hmul (hzeta.trans
    (congrArg₂ (fun (a : Γ((cU D).toScheme, OO D M W₃)) (z : (TB ((cU D).ι ≫ f)).Total
        (op (OO D M W₃))) =>
      sm ((cU D).ι ≫ f) (OO D M W₃) a * ((TB ((cU D).ι ≫ f)).incl 1
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.map
            (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
              (inf_le_left : W₃ ⊓ cU' D M ≤ W₃))).op (G1.rs f D 1 k₂ ξ₀)) * z) +
        δ ((cU D).ι ≫ f) (OO D M W₃) a * z + sm ((cU D).ι ≫ f) (OO D M W₃) a *
          Δ ((cU D).ι ≫ f) (OO D M W₃) p z) hh' hz'))

/-- **`∇` preserves `C^•`**, given generator data near every point. -/
theorem nabStable_of_genData (hSD : ∀ E ∈ S.support, E ∈ D.support)
    (hGD : ∀ y : X, ∃ W₂ : X.Opens, y ∈ W₂ ∧ ∃ g₀ ξ₀, GenData n f D hD M uu cc W₂ g₀ ξ₀) :
    NabStable n f D hD S M uu cc := by
  intro p W ω hω y hy
  obtain ⟨W₁, h₁, hy₁, m, g, η, hg, hη, he⟩ := hω y hy
  obtain ⟨W₂, hy₂, g₀, ξ₀, hG₁, hG₂, hG₃, hG₄⟩ := hGD y
  obtain ⟨W₃, hy₃, hW₃, hmon⟩ := exists_affine_monSet n f D hD M _ η hη hy₁
    ((W₁ : X.Opens) ⊓ W₂) ⟨hy₁, hy₂⟩
  have k₁ : (W₃ : X.Opens) ≤ W₁ := hW₃.trans inf_le_left
  have k₂ : (W₃ : X.Opens) ≤ W₂ := hW₃.trans inf_le_right
  refine ⟨W₃, k₁.trans h₁, hy₃, ?_⟩
  change LocalRep n f D hD S M (p + 1) W₃ _
  have hchart := exists_chart_suppIdeal n f D S hD hSD
  have hrO : rO f (D := D) (M := M) ((p + 1 : ℕ) : ℤ) (k₁.trans h₁)
      (nab ((cU D).ι ≫ f) p (θW f D M uu cc W) ω) =
      nab ((cU D).ι ≫ f) p (θW f D M uu cc W₃) (rO f p (k₁.trans h₁) ω) :=
    (nab_map _ p _ _).trans (congrArg (fun θ => nab ((cU D).ι ≫ f) p θ _) (θW_restrict f D M uu cc
        (k₁.trans h₁)))
  have he₃ := (congrArg ((TB ((cU D).ι ≫ f)).incl (p : ℤ))
    (rO_rO f (D := D) (M := M) (p : ℤ) h₁ k₁ ω)).symm.trans (sum_rep_restrict f D M k₁ g η he)
  choose hh hhe using fun i => hG₃ W₃ k₂ _ (DivCond.restrict D M k₁ (hg i))
  set g₀' := X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) k₂)).op g₀
  set ψ₃ := (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
    (inf_le_left : (W₃ : X.Opens) ⊓ cU' D M ≤ W₃))).op
  have hξ := genData_nab_restrict f D M uu cc k₂ hG₄
  refine ⟨m, fun _ => g₀', fun i => zetaForm f D p W₃ (hh i) (G1.rs f D 1 k₂ ξ₀)
    (G1.rs f D p k₁ (η i)), fun _ => hG₁.restrict D M k₂, fun i => zetaForm_mem n f D hD S hchart p
      W₃ (hh i) _ _ (G1.relativeLogForms_restrict n f D hD _ 1 k₂ hG₂)
      (G1.relativeLogForms_restrict n f D hD _ p k₁ (hη i)), ?_⟩
  refine (congrArg ((TB ((cU D).ι ≫ f)).incl ((p + 1 : ℕ) : ℤ)) hrO).trans ?_
  refine (twT_incl p _ _).symm.trans ?_
  rw [he₃, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨hk, hz⟩ := hmon i (Finset.mem_univ i)
  exact nab_summand_eq f D M uu cc p k₁ k₂ (g i) (hh i) g₀ ξ₀ (η i) (hhe i) hk hz hξ

/-- **Generator data exists near every point.** -/
theorem exists_genData [CompactSpace X] (hMC : M.IsCartier) (Bn : Divisor X) (N : ℕ)
    (ψ : (RationalFunctions X)ˣ) (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (hu : (toRationalFunctionsPresheaf X).app (op (cU' D M)) uu = ratRes (cU' D M) ψ)
    (hcc : cc * ((N : Γ(X, cU' D M)) * uu) = 1) (hNW : ∀ W : X.Opens, IsUnit (N : Γ(X, W)))
    (hN0 : N ≠ 0) (hBn : ∀ E, 0 ≤ Bn E) (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support) (y : X) :
    ∃ W₂ : X.Opens, y ∈ W₂ ∧ ∃ g₀ ξ₀, GenData n f D hD M uu cc W₂ g₀ ξ₀ := by
  classical
  obtain ⟨W₂, hy₂, r, τ, j, v, g₀, -, hjD, hτ, -, hvu, hg₀div, hg₀gen, hX⟩ :=
    exists_generator_factorization n f D hD M uu hMC Bn N ψ hψ hu hBn hBD y
  set b : Fin r → ℕ := fun k => (Bn (j k)).toNat
  set Ni : Γ(X, (W₂ : X.Opens)) := ((hNW W₂).unit⁻¹ : (Γ(X, (W₂ : X.Opens)))ˣ).val
  set vi : Γ(X, (W₂ : X.Opens)) := (hvu.unit⁻¹ : (Γ(X, (W₂ : X.Opens)))ˣ).val
  have hsu : ∀ k, IsUnit (((cU D).ι.app W₂).hom (τ k)) := fun k =>
    B1.isUnit_res_of_ideal_eq D (hjD k) (hτ k)
  set sk : Fin r → Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W₂ : X.Opens)) := fun k =>
    ((hsu k).unit⁻¹ : (Γ((cU D).toScheme, (cU D).ι ⁻¹ᵁ (W₂ : X.Opens)))ˣ).val
  have hsk : ∀ k, sk k * ((cU D).ι.app W₂).hom (τ k) = 1 := fun k => (hsu k).val_inv_mul
  let ξ₀ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece 1).val.obj
      (op ((cU D).ι ⁻¹ᵁ (W₂ : X.Opens))) :=
    asStr (((cU D).ι.app W₂).hom Ni) •
      (asStr (((cU D).ι.app W₂).hom vi) • dF f D _ (((cU D).ι.app W₂).hom v) +
        ∑ k, b k • (asStr (sk k) • dF f D _ (((cU D).ι.app W₂).hom (τ k))))
  have hξ : ξ₀ ∈ relativeLogForms n f D hD ⊤ 1 W₂ :=
    G1.smul_mem_relativeLogForms n f D hD _ _ Ni (G1.add_mem_relativeLogForms n f D hD _ _
      (G1.smul_mem_relativeLogForms n f D hD _ _ vi (B1.δ_mem_relativeLogForms f D n hD _ v))
      (B1.sum_mem_relativeLogForms f D n hD _ _ _ _ _ fun k _ =>
        B1.nsmul_mem_relativeLogForms f D n hD _ _ _ _
          (B1.dlog_mem_relativeLogForms f D n hD (hjD k) (hτ k) (sk k) (hsk k))))
  refine ⟨W₂, hy₂, g₀, ξ₀, hg₀div, hξ, hg₀gen, ?_⟩
  let ρ : Γ(X, (W₂ : X.Opens)) →+* Γ((cU D).toScheme, OO D M W₂) :=
    ((cU D).ι.app ((W₂ : X.Opens) ⊓ cU' D M)).hom.comp (X.presheaf.map (homOfLE inf_le_left).op).hom
  let ρ' : Γ(X, cU' D M) →+* Γ((cU D).toScheme, OO D M W₂) :=
    ((cU D).ι.app ((W₂ : X.Opens) ⊓ cU' D M)).hom.comp (X.presheaf.map (homOfLE
        inf_le_right).op).hom
  set gg := ((cU D).ι.app ((W₂ : X.Opens) ⊓ cU' D M)).hom g₀
  have hrel : gg ^ N = ρ' uu * ρ v * ρ (∏ k, τ k ^ b k) := by
    have := congrArg ((cU D).ι.app ((W₂ : X.Opens) ⊓ cU' D M)).hom hX
    simp only [map_pow, map_mul] at this
    rw [this, mul_assoc]
    rfl
  set ψ₂ := (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
    (inf_le_left : (W₂ : X.Opens) ⊓ cU' D M ≤ W₂))).op
  have hres : ∀ a : Γ(X, (W₂ : X.Opens)),
      (cU D).toScheme.presheaf.map ψ₂ (((cU D).ι.app W₂).hom a) = ρ a := fun a =>
    G1.app_restrict inf_le_left a
  set sk' : Fin r → Γ((cU D).toScheme, OO D M W₂) := fun k => (cU D).toScheme.presheaf.map ψ₂ (sk k)
  have hsk' : ∀ k, sk' k * ρ (τ k) = 1 := fun k => by
    rw [← hres, ← map_mul, hsk, map_one]
  have hu' : (ρ' cc * N) * ρ' uu = 1 := by
    have := congrArg ρ' hcc
    rw [map_mul, map_mul, map_natCast, map_one] at this
    rw [← this]; ring
  have hv' : ρ vi * ρ v = 1 := by rw [← map_mul, hvu.val_inv_mul, map_one]
  have hN' : ρ Ni * (N : Γ((cU D).toScheme, OO D M W₂)) = 1 := by
    rw [← map_natCast ρ, ← map_mul, (hNW W₂).val_inv_mul, map_one]
  have hβprod : ρ (∏ k, τ k ^ b k) = ∏ k, ρ (τ k) ^ b k := by rw [map_prod]; simp only [map_pow]
  have hβ' : (∏ k, sk' k ^ b k) * ρ (∏ k, τ k ^ b k) = 1 := by
    rw [hβprod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [← mul_pow, hsk' k, one_pow]
  have hgu : IsUnit gg := by
    have h1 : IsUnit (gg ^ N) := by
      rw [hrel]
      exact ((IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hu')).mul
        (IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hv'))).mul
        (IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hβ'))
    exact (isUnit_pow_iff hN0).mp h1
  have hc : ρ' cc = ρ Ni * (ρ' cc * N) := by
    rw [mul_comm (ρ' cc), ← mul_assoc, hN', one_mul]
  have key := dlog_twist_identity (g := (cU D).ι ≫ f) (O := OO D M W₂) N hu' hv' hβ'
    hgu.unit.inv_mul hN' hc hrel
  rw [incl_θW]
  refine key.trans (congrArg _ ?_)
  rw [hβprod, dl_prod_pow Finset.univ (fun k => ρ (τ k)) sk' hsk' b]
  refine Eq.symm ((incl_map_smul _ 1 _ _).trans ?_)
  refine congrArg₂ (· * ·) (congrArg _ (hres Ni)) ?_
  rw [map_add, map_sum]
  refine ((TB ((cU D).ι ≫ f)).incl_add _ _ _).trans (congrArg₂ (· + ·) ?_ ?_)
  · refine (incl_map_smul _ 1 _ _).trans ?_
    unfold dl
    refine congrArg₂ (· * ·) (congrArg _ (hres vi)) ?_
    exact (congrArg ((TB ((cU D).ι ≫ f)).incl 1) (dF_restrict f D ψ₂ _)).trans
      (congrArg (δ ((cU D).ι ≫ f) (OO D M W₂)) (hres v))
  · refine (incl_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_nsmul]
    refine (map_nsmul (DirectSum.of _ (1 : ℤ)) _ _).trans (congrArg _ ?_)
    refine (incl_map_smul _ 1 _ _).trans ?_
    unfold dl
    refine congrArg₂ (· * ·) rfl ?_
    exact (congrArg ((TB ((cU D).ι ≫ f)).incl 1) (dF_restrict f D ψ₂ _)).trans
      (congrArg (δ ((cU D).ι ≫ f) (OO D M W₂)) (hres (τ k)))

end Stability

end MMP.FourfoldProofs.FractionalLogComplexProof
