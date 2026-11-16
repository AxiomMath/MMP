module

public import MMP.Analysis.Complex.WeierstrassDivision
public import MMP.AlgebraicGeometry.AnalytificationStalk
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Flatness of the analytification

The ring `ℂ{z₁, …, zₙ}` of holomorphic germs at the origin is flat over the polynomial ring
`ℂ[z₁, …, zₙ]`. Both have the formal power series ring `ℂ[[z₁, …, zₙ]]` as completion: the
completion of `ℂ{z}` at its maximal ideal is flat over `ℂ[z]`, being the `(z)`-adic completion of
the Noetherian ring `ℂ[z]`, and it is faithfully flat over the local Noetherian ring `ℂ{z}`.
Flatness descends along a faithfully flat extension. Translation carries the germs at any point
`p` to those at `0`. Base change by the ideal `I` of a chart `Γ(X, U) = ℂ[z]/I` and localization
then show that `𝒪_{X,y} → 𝒪_{ℂⁿ,p}/I 𝒪_{ℂⁿ,p} ≅ 𝒪_{X^an,y}` is flat.

## Main definitions

* `MMP.Analytic.holGermsTranslate`: holomorphic germs at `p` are those at `0`, by translation.
* `MMP.Analytic.mvPolynomialTranslate`: the translation `q(z) ↦ q(z + p)` of polynomials.

## Main results

* `MMP.flat_of_flat_of_faithfullyFlat`: if `A → B → C` with `C` flat over `A` and faithfully flat
  over `B`, then `B` is flat over `A`.
* `MMP.Analytic.flat_polyGermHom_zero`, `MMP.Analytic.flat_polyGermHom`: the germs at any point
  of `ℂⁿ` are flat over `ℂ[z₁, …, zₙ]`.
* `MMP.Analytic.Chart.flat_toStalkRing`, `MMP.Analytic.Chart.flat_stalkHom`: the local ring of a
  chart is flat over `Γ(X, U)` and over `𝒪_{X,y}`.
* `MMP.Analytic.flat_stalkMap_analytificationHom`: `𝒪_{X,y} → 𝒪_{X^an,y}` is flat.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*], §2.
-/

@[expose] public noncomputable section

open TensorProduct IsLocalRing

universe u v w

namespace MMP

/-- **Descent of flatness.** If `C` is flat over `A` and faithfully flat over an intermediate
`A`-algebra `B`, then `B` is flat over `A`. -/
theorem flat_of_flat_of_faithfullyFlat {A : Type u} {B : Type v} {C : Type w} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Flat A C] [Module.FaithfullyFlat B C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap'.{u}]
  intro (N : Type u) (N' : Type u) _ _ _ _ f hf
  have key : ∀ x : C ⊗[B] (B ⊗[A] N),
      AlgebraTensorModule.cancelBaseChange A B C C N' ((f.baseChange B).lTensor C x) =
        f.lTensor C (AlgebraTensorModule.cancelBaseChange A B C C N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul b n => simp [AlgebraTensorModule.cancelBaseChange_tmul]
  have hC : Function.Injective (f.lTensor C) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have h2 : Function.Injective ((f.baseChange B).lTensor C) := by
    intro x y hxy
    apply (AlgebraTensorModule.cancelBaseChange A B C C N).injective
    apply hC
    rw [← key, ← key, hxy]
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective B C (f.baseChange B)).1 h2

/-- If every element of `B` is congruent to an element of the image of `A` modulo `I B`, then
the same holds modulo `I ^ k B` for every `k`. -/
theorem exists_sub_mem_map_pow {A : Type u} {B : Type v} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (hsurj : ∀ b, ∃ a, b - φ a ∈ I.map φ) (k : ℕ) (b : B) :
    ∃ a, b - φ a ∈ (I ^ k).map φ := by
  induction k generalizing b with
  | zero => exact ⟨0, by rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih b
    suffices H : ∀ x ∈ (I ^ k).map φ, ∀ c : B, ∃ a', c * x - φ a' ∈ (I ^ (k + 1)).map φ by
      obtain ⟨a', ha'⟩ := H _ ha 1
      refine ⟨a + a', ?_⟩
      rw [one_mul] at ha'
      convert ha' using 1
      rw [map_add]
      ring
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      intro c
      obtain ⟨a', ha'⟩ := hsurj c
      refine ⟨a' * i, ?_⟩
      rw [show c * φ i - φ (a' * i) = (c - φ a') * φ i by rw [map_mul, sub_mul],
        pow_succ', Ideal.map_mul]
      exact Ideal.mul_mem_mul ha' (Ideal.mem_map_of_mem φ hi)
    | zero => exact fun c => ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro c
      obtain ⟨a₁, h₁⟩ := hx c
      obtain ⟨a₂, h₂⟩ := hy c
      refine ⟨a₁ + a₂, ?_⟩
      convert Ideal.add_mem _ h₁ h₂ using 1
      rw [map_add]
      ring
    | smul d x _ hx =>
      intro c
      obtain ⟨a', h⟩ := hx (c * d)
      exact ⟨a', by simpa [smul_eq_mul, mul_assoc] using h⟩

/-- **Jets along a faithfully flat map.** Let `φ : A → B` be faithfully flat and `I` an ideal of
`A` such that `A → B / I B` is surjective. Then `A / I ^ N ≅ B / (I B) ^ N` for every `N`. -/
theorem exists_ringEquiv_quotient_pow_of_faithfullyFlat {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] (φ : A →+* B) (hφ : φ.FaithfullyFlat) (I : Ideal A) (J : Ideal B)
    (hIJ : I.map φ = J) (hsurj : ∀ b, ∃ a, b - φ a ∈ J) (N : ℕ) :
    ∃ e : A ⧸ I ^ N ≃+* B ⧸ J ^ N,
      ∀ a, e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a) := by
  subst hIJ
  rw [← Ideal.map_pow]
  have hc : ((I ^ N).map φ).comap φ = I ^ N := by
    algebraize [φ]
    exact Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (I ^ N)
  refine ⟨RingEquiv.ofBijective (Ideal.quotientMap _ φ hc.ge)
    ⟨Ideal.quotientMap_injective' hc.le, ?_⟩, fun a => ?_⟩
  · intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := exists_sub_mem_map_pow φ I hsurj N b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, ← neg_sub]
    exact (Ideal.neg_mem_iff _).2 ha
  · rfl

/-- For a local homomorphism `φ : A → B` of local rings such that every element of `B` is
congruent to an element of the image of `A` modulo `𝔪_A B`, the maximal ideal of `B` is
`𝔪_A B`. -/
theorem map_maximalIdeal_eq_of_forall_exists_sub_mem {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (hsurj : ∀ b, ∃ a, b - φ a ∈ (maximalIdeal A).map φ) :
    (maximalIdeal A).map φ = maximalIdeal B := by
  refine le_antisymm (IsLocalRing.map_maximalIdeal_le φ) fun b hb => ?_
  obtain ⟨a, ha⟩ := hsurj b
  have hφa : φ a ∈ maximalIdeal B := by
    simpa using Ideal.sub_mem _ hb (IsLocalRing.map_maximalIdeal_le φ ha)
  have ha' : a ∈ maximalIdeal A := by rwa [← IsLocalRing.maximalIdeal_comap φ]
  simpa using Ideal.add_mem _ ha (Ideal.mem_map_of_mem φ ha')

/-- **Jets of a faithfully flat local homomorphism.** If `φ : A → B` is a faithfully flat local
homomorphism of local rings and `A → B / 𝔪_A B` is surjective, then
`A / 𝔪_A ^ N ≅ B / 𝔪_B ^ N` for every `N`, compatibly with `φ`. -/
theorem exists_ringEquiv_quotient_maximalIdeal_pow {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (hφ : φ.FaithfullyFlat) (hsurj : ∀ b, ∃ a, b - φ a ∈ (maximalIdeal A).map φ) (N : ℕ) :
    ∃ e : A ⧸ maximalIdeal A ^ N ≃+* B ⧸ maximalIdeal B ^ N,
      ∀ a, e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a) :=
  exists_ringEquiv_quotient_pow_of_faithfullyFlat φ hφ _ _
    (map_maximalIdeal_eq_of_forall_exists_sub_mem φ hsurj)
    (fun b => (map_maximalIdeal_eq_of_forall_exists_sub_mem φ hsurj) ▸ hsurj b) N

namespace Analytic

/-- `ℂ{z₁, …, zₙ}` is flat over `ℂ[z₁, …, zₙ]`, via the germs of polynomials. -/
theorem flat_polyGermHom_zero (n : ℕ) : (polyGermHom (0 : Fin n → ℂ)).Flat := by
  let _ := (polyGermHom (0 : Fin n → ℂ)).toAlgebra
  change (algebraMap (MvPolynomial (Fin n) ℂ) (holGerms (0 : Fin n → ℂ))).Flat
  rw [RingHom.flat_algebraMap_iff]
  obtain ⟨hreg, -, -, e, he⟩ := isRegularLocalRing_holGerms n
  let B := holGerms (0 : Fin n → ℂ)
  let C := AdicCompletion (maximalIdeal B) B
  have : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let eL : C ≃ₐ[MvPolynomial (Fin n) ℂ] MvPowerSeries (Fin n) ℂ :=
    AlgEquiv.ofRingEquiv (f := e) fun q => by
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ) B C]
      erw [he q]
      rw [MvPowerSeries.algebraMap_apply']
      simp
  have : Module.Flat (MvPolynomial (Fin n) ℂ) (MvPowerSeries (Fin n) ℂ) :=
    Module.Flat.of_linearEquiv (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ).toLinearEquiv
  have : Module.Flat (MvPolynomial (Fin n) ℂ) C := Module.Flat.of_linearEquiv eL.toLinearEquiv
  exact flat_of_flat_of_faithfullyFlat (A := MvPolynomial (Fin n) ℂ) (B := B) (C := C)

section Translation

variable {n : ℕ}

/-- The translation `z ↦ z + p` of `ℂⁿ` tends to `p` along the neighbourhoods of `0`. -/
lemma tendsto_add_const_nhds_zero (p : Fin n → ℂ) :
    Filter.Tendsto (fun z : Fin n → ℂ => z + p) (nhds 0) (nhds p) := by
  have h : Filter.Tendsto (fun z : Fin n → ℂ => z + p) (nhds 0) (nhds (0 + p)) :=
    Filter.tendsto_id.add_const p
  rwa [zero_add] at h

/-- The translation `z ↦ z - p` of `ℂⁿ` tends to `0` along the neighbourhoods of `p`. -/
lemma tendsto_sub_const_nhds (p : Fin n → ℂ) :
    Filter.Tendsto (fun z : Fin n → ℂ => z - p) (nhds p) (nhds 0) := by
  have h : Filter.Tendsto (fun z : Fin n → ℂ => z - p) (nhds p) (nhds (p - p)) :=
    Filter.tendsto_id.sub_const p
  rwa [sub_self] at h

/-- Translation `z ↦ z + p` identifies the holomorphic germs at `p` with those at `0`. -/
def holGermsTranslate (p : Fin n → ℂ) : holGerms p ≃+* holGerms (0 : Fin n → ℂ) :=
  RingEquiv.ofRingHom
    (holPullback (fun z => z + p) (differentiable_id.add_const p) (tendsto_add_const_nhds_zero p))
    (holPullback (fun z => z - p) (differentiable_id.sub_const p) (tendsto_sub_const_nhds p))
    (by
      ext g
      obtain ⟨f, hf, -⟩ := g.2
      simp only [RingHom.coe_comp, Function.comp_apply, coe_holPullback, ← hf,
        Filter.Germ.coe_compTendsto, RingHom.id_apply]
      congr 1
      funext z
      simp)
    (by
      ext g
      obtain ⟨f, hf, -⟩ := g.2
      simp only [RingHom.coe_comp, Function.comp_apply, coe_holPullback, ← hf,
        Filter.Germ.coe_compTendsto, RingHom.id_apply]
      congr 1
      funext z
      simp)

/-- Translation `q(z) ↦ q(z + p)` of polynomials, as a ring automorphism. -/
def mvPolynomialTranslate (p : Fin n → ℂ) : MvPolynomial (Fin n) ℂ ≃+* MvPolynomial (Fin n) ℂ :=
  RingEquiv.ofRingHom
    (MvPolynomial.bind₁ fun i => MvPolynomial.X i + MvPolynomial.C (p i)).toRingHom
    (MvPolynomial.bind₁ fun i => MvPolynomial.X i - MvPolynomial.C (p i)).toRingHom
    (by
      apply MvPolynomial.ringHom_ext <;> intro <;> simp)
    (by
      apply MvPolynomial.ringHom_ext <;> intro <;> simp)

/-- Translating the germ at `p` of a polynomial `q` gives the germ at `0` of the translated
polynomial `z ↦ q(z + p)`. -/
lemma holGermsTranslate_polyGermHom (p : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) :
    holGermsTranslate p (polyGermHom p q) = polyGermHom 0 (mvPolynomialTranslate p q) := by
  apply Subtype.ext
  simp only [holGermsTranslate, RingEquiv.ofRingHom_apply, coe_holPullback, coe_polyGermHom,
    Filter.Germ.coe_compTendsto]
  congr 1
  funext z
  have h : MvPolynomial.eval (z + p) = (MvPolynomial.eval z).comp
      (MvPolynomial.bind₁ fun i => MvPolynomial.X i + MvPolynomial.C (p i)).toRingHom := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp
  exact RingHom.congr_fun h q

/-- The holomorphic germs at any point `p` of `ℂⁿ` are flat over the polynomials. -/
theorem flat_polyGermHom (p : Fin n → ℂ) : (polyGermHom p).Flat := by
  have h : polyGermHom p = (holGermsTranslate p).symm.toRingHom.comp
      ((polyGermHom (0 : Fin n → ℂ)).comp (mvPolynomialTranslate p).toRingHom) := by
    ext q <;> simp [← holGermsTranslate_polyGermHom]
  rw [h]
  exact RingHom.Flat.respectsIso.1 _ _ (RingHom.Flat.respectsIso.2 _ _ (flat_polyGermHom_zero n))

end Translation

section Chart

open CategoryTheory AlgebraicGeometry ComplexPoints Analytification

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- The local ring `𝒪_{ℂⁿ,p}/I 𝒪_{ℂⁿ,p}` of a chart is flat over `Γ(X, U) = ℂ[z]/I`: it is the
base change of the flat `ℂ[z]`-algebra `𝒪_{ℂⁿ,p}`. -/
theorem Chart.flat_toStalkRing (c : Chart sX) (p : Fin c.n → ℂ) : (c.toStalkRing p).Flat := by
  let _ := (polyGermHom p).toAlgebra
  have : Module.Flat (MvPolynomial (Fin c.n) ℂ) (holGerms p) := flat_polyGermHom p
  have : Module.Flat (MvPolynomial (Fin c.n) ℂ ⧸ c.ideal)
      (holGerms p ⧸ c.ideal.map (algebraMap (MvPolynomial (Fin c.n) ℂ) (holGerms p))) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (holGerms p) c.ideal).toLinearEquiv
  have hq := RingHom.flat_algebraMap_iff.2 this
  let e : Γ(X, c.U) ≃+* MvPolynomial (Fin c.n) ℂ ⧸ c.ideal :=
    (RingHom.quotientKerEquivOfSurjective c.surjective).symm
  have h : c.toStalkRing p = (algebraMap (MvPolynomial (Fin c.n) ℂ ⧸ c.ideal)
      (holGerms p ⧸ c.ideal.map (algebraMap (MvPolynomial (Fin c.n) ℂ) (holGerms p)))).comp
        e.toRingHom := by
    ext f
    obtain ⟨q, rfl⟩ := c.surjective f
    have he : e (c.pres q) = Ideal.Quotient.mk c.ideal q :=
      (RingEquiv.symm_apply_eq _).2 (RingHom.quotientKerEquivOfSurjective_apply_mk _ _).symm
    change c.toStalkRing p (c.pres q) = algebraMap (MvPolynomial (Fin c.n) ℂ ⧸ c.ideal)
      (holGerms p ⧸ c.ideal.map (algebraMap (MvPolynomial (Fin c.n) ℂ) (holGerms p))) (e (c.pres q))
    rw [he, c.toStalkRing_pres]
    rfl
  rw [h]
  exact RingHom.Flat.respectsIso.2 _ _ hq

/-- The homomorphism `𝒪_{X,y} → 𝒪_{ℂⁿ,z(y)}/I 𝒪_{ℂⁿ,z(y)}` of a chart is flat. -/
theorem Chart.flat_stalkHom (c : Chart sX) (y : chart (sX := sX) c.U) : (c.stalkHom y).Flat := by
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := c.U)
    ⟨y.1.toScheme, mem_chart_iff.1 y.2⟩
  have := c.isAffineOpen.isLocalization_stalk ⟨y.1.toScheme, mem_chart_iff.1 y.2⟩
  let _ := (c.stalkHom y).toAlgebra
  let _ := (c.toStalkRing (c.coords y)).toAlgebra
  have : IsScalarTower Γ(X, c.U) (X.presheaf.stalk y.1.toScheme) (c.StalkRing (c.coords y)) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.stalkHom_germ y a).symm
  have : Module.Flat Γ(X, c.U) (c.StalkRing (c.coords y)) := c.flat_toStalkRing (c.coords y)
  change (algebraMap (X.presheaf.stalk y.1.toScheme) (c.StalkRing (c.coords y))).Flat
  rw [RingHom.flat_algebraMap_iff]
  exact (Module.flat_iff_of_isLocalization (X.presheaf.stalk y.1.toScheme)
    (c.isAffineOpen.primeIdealOf ⟨y.1.toScheme, mem_chart_iff.1 y.2⟩).asIdeal.primeCompl
    (c.StalkRing (c.coords y))).2 inferInstance

/-- Every holomorphic germ at `p` is congruent to a constant modulo the ideal generated by the
coordinate germs `zᵢ - pᵢ` (Hadamard division). -/
theorem exists_sub_polyGermHom_C_mem_span {n : ℕ} (p : Fin n → ℂ) (g : holGerms p) :
    ∃ v : ℂ, g - polyGermHom p (MvPolynomial.C v) ∈
      Ideal.span (Set.range fun i => polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i))) := by
  obtain ⟨f, hf, -⟩ := g.2
  refine ⟨f p, ?_⟩
  have h := holPullbackAt_sub_mem (F := Fin n → ℂ) (a := p) (b := p) (A := id)
    (B := fun _ => p) (Filter.Eventually.of_forall fun _ => differentiableAt_id) Filter.tendsto_id
    (Filter.Eventually.of_forall fun _ => differentiableAt_const p) tendsto_const_nhds rfl rfl
    (Ideal.span (Set.range fun i => polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i))))
    (fun i => ⟨_, Ideal.subset_span ⟨i, rfl⟩, by simp; rfl⟩) g
  rw [holPullbackAt_id] at h
  convert h using 2
  apply Subtype.ext
  simp only [coe_polyGermHom, MvPolynomial.eval_C, coe_holPullbackAt, ← hf]
  rfl

/-- In the local ring of a chart, every element is congruent to the image of an element of
`𝒪_{X,y}` modulo `𝔪_{X,y}`: the residue field is `ℂ` and the maximal ideal is generated by the
coordinates. -/
theorem Chart.exists_sub_stalkHom_mem (c : Chart sX) (y : chart (sX := sX) c.U)
    (x : c.StalkRing (c.coords y)) :
    ∃ a, x - c.stalkHom y a ∈
      (maximalIdeal (X.presheaf.stalk y.1.toScheme)).map (c.stalkHom y) := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := c.ideal.map (polyGermHom (c.coords y))) x
  obtain ⟨v, hv⟩ := exists_sub_polyGermHom_C_mem_span (c.coords y) g
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := c.U)
    ⟨y.1.toScheme, mem_chart_iff.1 y.2⟩
  have := c.isAffineOpen.isLocalization_stalk ⟨y.1.toScheme, mem_chart_iff.1 y.2⟩
  refine ⟨X.presheaf.germ c.U y.1.toScheme (mem_chart_iff.1 y.2) (c.pres (MvPolynomial.C v)), ?_⟩
  rw [c.stalkHom_germ, c.toStalkRing_pres]
  have hle : (Ideal.span (Set.range fun i => polyGermHom (c.coords y)
      (MvPolynomial.X i - MvPolynomial.C (c.coords y i)))).map (StalkRing.mk c (c.coords y)) ≤
      (maximalIdeal (X.presheaf.stalk y.1.toScheme)).map (c.stalkHom y) := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hi : X.presheaf.germ c.U y.1.toScheme (mem_chart_iff.1 y.2)
        (c.pres (MvPolynomial.X i - MvPolynomial.C (c.coords y i))) ∈
        maximalIdeal (X.presheaf.stalk y.1.toScheme) := by
      refine (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk y.1.toScheme)
        (c.isAffineOpen.primeIdealOf ⟨y.1.toScheme, mem_chart_iff.1 y.2⟩).asIdeal _).2 ?_
      by_contra hn
      apply evalHom_ne_zero_of_notMem c.isAffineOpen y _ hn
      rw [c.evalHom_pres]
      simp
    have := Ideal.mem_map_of_mem (c.stalkHom y) hi
    rwa [c.stalkHom_germ, c.toStalkRing_pres] at this
  apply hle
  have := Ideal.mem_map_of_mem (StalkRing.mk c (c.coords y)) hv
  rwa [map_sub] at this

/-- Near a `ℂ`-point, the stalk map of the analytification is the stalk homomorphism of a chart
up to a ring isomorphism. -/
theorem exists_chart_ringEquiv_comp_stalkMap [LocallyOfFiniteType sX] (y : ComplexPoints sX) :
    ∃ (c : Chart sX) (hy : y ∈ chart (sX := sX) c.U)
      (e : (analytification sX).presheaf.stalk y ≃+* c.StalkRing (c.coords ⟨y, hy⟩)),
      e.toRingHom.comp ((analytificationHom sX).hom.stalkMap y).hom = c.stalkHom ⟨y, hy⟩ := by
  obtain ⟨U, hU, hyU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show y.toScheme ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨c, rfl⟩ := Chart.exists_eq (sX := sX) hU
  have hy : y ∈ chart (sX := sX) c.U := mem_chart_iff.2 hyU
  obtain ⟨e, he⟩ := Chart.exists_stalk_ringEquiv y c hy
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := c.U) ⟨y.toScheme, hyU⟩
  have := c.isAffineOpen.isLocalization_stalk ⟨y.toScheme, hyU⟩
  refine ⟨c, hy, e, IsLocalization.ringHom_ext (S := X.presheaf.stalk y.toScheme)
    (c.isAffineOpen.primeIdealOf ⟨y.toScheme, hyU⟩).asIdeal.primeCompl ?_⟩
  ext f
  exact (he f).trans (c.stalkHom_germ ⟨y, hy⟩ f).symm

/-- The stalk map `𝒪_{X,y} → 𝒪_{X^an,y}` of the analytification is surjective modulo
`𝔪_{X,y} 𝒪_{X^an,y}`. -/
theorem exists_sub_stalkMap_analytificationHom_mem [LocallyOfFiniteType sX]
    (y : ComplexPoints sX) (b : (analytification sX).presheaf.stalk y) :
    ∃ a, b - ((analytificationHom sX).hom.stalkMap y).hom a ∈
      (maximalIdeal (X.presheaf.stalk y.toScheme)).map
        ((analytificationHom sX).hom.stalkMap y).hom := by
  obtain ⟨c, hy, e, key⟩ := exists_chart_ringEquiv_comp_stalkMap y
  let φ : X.presheaf.stalk y.toScheme →+* (analytification sX).presheaf.stalk y :=
    ((analytificationHom sX).hom.stalkMap y).hom
  replace key : e.toRingHom.comp φ = c.stalkHom ⟨y, hy⟩ := key
  obtain ⟨a, ha⟩ := c.exists_sub_stalkHom_mem ⟨y, hy⟩ (e b)
  rw [← key, ← Ideal.map_map] at ha
  refine ⟨a, Ideal.apply_mem_of_equiv_iff.1 (?_ : e (b - φ a) ∈ _)⟩
  rw [map_sub]
  exact ha

/-- The stalk map `𝒪_{X,y} → 𝒪_{X^an,y}` of the analytification is flat. -/
theorem flat_stalkMap_analytificationHom [LocallyOfFiniteType sX] (y : ComplexPoints sX) :
    ((analytificationHom sX).hom.stalkMap y).hom.Flat := by
  obtain ⟨c, hy, e, key⟩ := exists_chart_ringEquiv_comp_stalkMap y
  let φ : X.presheaf.stalk y.toScheme →+* (analytification sX).presheaf.stalk y :=
    ((analytificationHom sX).hom.stalkMap y).hom
  replace key : e.toRingHom.comp φ = c.stalkHom ⟨y, hy⟩ := key
  have h : φ = e.symm.toRingHom.comp (c.stalkHom ⟨y, hy⟩) := by
    rw [← key]
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  change φ.Flat
  rw [h]
  exact RingHom.Flat.respectsIso.1 _ _ (c.flat_stalkHom ⟨y, hy⟩)

end Chart

end Analytic

end MMP
