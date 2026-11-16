module
public import MMP.AlgebraicGeometry.AnalytificationStalk
public import MMP.AlgebraicGeometry.Normalization.Completion

/-!
# The algebraic and the analytic local ring of a complex variety

Let `X` be a complex variety, `y` a `ℂ`-point of `X` (equivalently, a closed point), and write
`A = 𝒪_{X,y}` and `B = 𝒪_{X^an,y}` for the algebraic and the analytic local rings, related by the
stalk map `φ : A → B` of the comparison morphism `α_X : X^an → X`. Then `B` is a Noetherian
local ring, `φ` is faithfully flat, `𝔪_A B = 𝔪_B`, and `φ` induces isomorphisms
`A/𝔪_A^N ≅ B/𝔪_B^N` for every `N`. Consequently `A` and `B` have the same Krull dimension, the
same embedding dimension and the same completion, and extension and contraction along `φ` are
inverse bijections between the ideals containing `𝔪_A^N` and those containing `𝔪_B^N`. If `A`
is normal, then `B` is a normal domain. For any affine chart `Spec ℂ[z]/I` containing `y`, with
coordinates `p` of `y`, `B ≅ ℂ{z - p}/I ℂ{z - p}`; in particular a hypersurface germ `h = 0`
has local ring `ℂ{z - p}/(h)`.

Furthermore, `ℂ`-algebra homomorphisms between analytic local rings `ℂ{z - p}/I → ℂ{w - q}/J`
are exactly the pullbacks along holomorphic map germs `(ℂᵏ, q) → (ℂⁿ, p)` carrying `I` into
`J`, and the convergent germ ring `ℂ{z₁, …, zₘ}` is a regular local factorial ring such that a
surjection onto a local ring of embedding dimension `m` induces an isomorphism on cotangent
spaces.

## Main results

* `MMP.Analytic.analyticStalk_package`: the package above.

## Implementation notes

The analytic local ring is the stalk of `MMP.Analytic.analytification` at a `ℂ`-point, and the
canonical map is the stalk map of `MMP.Analytic.analytificationHom`. Every canonical map is
pinned by its value on generators: the jet and completion isomorphisms by compatibility with
`φ`, the chart isomorphism by compatibility with `MMP.Analytic.Chart.toStalkRing`, and the germ
correspondence by `MMP.Analytic.germPullback`. The embedding dimension of a local ring is the
minimal number of generators `Submodule.spanFinrank` of its maximal ideal, as in
`IsRegularLocalRing`; the cotangent statement is the injectivity of `𝔪/𝔪² → 𝔪_S/𝔪_S²`, its
surjectivity being automatic for a surjection. Statements whose instance arguments are
conclusions (`IsLocalRing B`, `IsDomain`) are stated as existentials over these instances.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*], §2.
* [Grauert, Remmert, *Coherent analytic sheaves*], Chapter 2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology Filter IsLocalRing TensorProduct

namespace MMP.Analytic

universe u

/-! ### Local homomorphisms with isomorphic jets -/

/-- If every element of `R` is congruent to an image modulo `M R`, it is congruent to an image
modulo `M^N R`, for every `N`. -/
private theorem exists_sub_mem_map_pow {P R : Type*} [CommRing P] [CommRing R] (f : P →+* R)
    (M : Ideal P) (h : ∀ r : R, ∃ a, r - f a ∈ M.map f) (N : ℕ) (r : R) :
    ∃ a, r - f a ∈ (M ^ N).map f := by
  induction N generalizing r with
  | zero => exact ⟨0, by simp [Ideal.map_top]⟩
  | succ N ih =>
    obtain ⟨a, ha⟩ := ih r
    suffices H : ∀ x ∈ (M ^ N).map f, ∃ b, x - f b ∈ (M ^ (N + 1)).map f by
      obtain ⟨b, hb⟩ := H _ ha
      exact ⟨a + b, by rwa [map_add, ← sub_sub]⟩
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, -, rfl⟩ := hx
      exact ⟨m, by simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨b, hb⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨b + c, by
        convert Ideal.add_mem _ hb hc using 1
        rw [map_add]
        ring⟩
    | smul s y hy ihy =>
      obtain ⟨b, hb⟩ := ihy
      obtain ⟨c, hc⟩ := h s
      refine ⟨c * b, ?_⟩
      have h1 : (s - f c) * y ∈ (M ^ (N + 1)).map f := by
        rw [pow_succ', Ideal.map_mul]
        exact Ideal.mul_mem_mul hc hy
      convert Ideal.add_mem _ h1 (Ideal.mul_mem_left _ (f c) hb) using 1
      rw [smul_eq_mul, map_mul]
      ring

/-- The projections of the adic completion are compatible with the transition maps. -/
private theorem factorPow_evalₐ {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I R x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  have := AdicCompletion.AdicCauchySequence.mk_eq_mk hle x
  rw [Submodule.Quotient.eq] at this
  exact Ideal.Quotient.eq.2 (by simpa [smul_eq_mul, Ideal.mul_top] using this)

/-- If `A → B → C`, with `C` faithfully flat over `B` and flat over `A`, then `B` is flat over
`A`. -/
private theorem flat_of_flat_of_faithfullyFlat {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.FaithfullyFlat B C] [Module.Flat A C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  rw [← LinearMap.baseChange_eq_ltensor]
  refine (Module.FaithfullyFlat.lTensor_injective_iff_injective B C
    (LinearMap.baseChange B f)).1 ?_
  have heq : ⇑((LinearMap.baseChange B f).lTensor C) =
      (AlgebraTensorModule.cancelBaseChange A B C C P).symm ∘ (f.lTensor C) ∘
        (AlgebraTensorModule.cancelBaseChange A B C C N) := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b n =>
        simp only [Function.comp_apply, LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
          AlgebraTensorModule.cancelBaseChange_tmul]
        rw [LinearEquiv.eq_symm_apply, AlgebraTensorModule.cancelBaseChange_tmul]
      | add y z hy hz => simp_all [tmul_add]
    | add x y hx hy => simp_all
  rw [heq]
  exact (AlgebraTensorModule.cancelBaseChange A B C C P).symm.injective.comp
    ((Module.Flat.lTensor_preserves_injective_linearMap f hf).comp
      (AlgebraTensorModule.cancelBaseChange A B C C N).injective)

/-- A ring with a faithfully flat map to an integrally closed domain is an integrally closed
domain. -/
private theorem isDomain_and_isIntegrallyClosed_of_faithfullyFlat (A B : Type*) [CommRing A]
    [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] [IsDomain B] [IsIntegrallyClosed B] :
    IsDomain A ∧ IsIntegrallyClosed A := by
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have : IsDomain A := hinj.isDomain _
  refine ⟨this, (isIntegrallyClosed_iff (FractionRing A)).mpr ?_⟩
  intro x hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  have hinjL : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj
  let ψ : FractionRing A →ₐ[A] FractionRing B :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId A (FractionRing B)) hinjL
  obtain ⟨c, hc⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp ((hx.map ψ).tower_top : IsIntegral B _)
  have hdvd : algebraMap A B (b : A) ∣ algebraMap A B a := by
    refine ⟨c, IsFractionRing.injective B (FractionRing B) ?_⟩
    have h := congrArg ψ (IsLocalization.mk'_spec (FractionRing A) a b)
    rw [map_mul, ψ.commutes, ψ.commutes, ← hc] at h
    rw [map_mul, ← IsScalarTower.algebraMap_apply A B (FractionRing B),
      ← IsScalarTower.algebraMap_apply A B (FractionRing B), mul_comm]
    exact h.symm
  rw [← Ideal.mem_span_singleton, ← Set.image_singleton, ← Ideal.map_span,
    ← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat,
    Ideal.mem_span_singleton] at hdvd
  obtain ⟨r, hr⟩ := hdvd
  exact ⟨r, by rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, mul_comm, ← hr]⟩

section AdicCompletionMap

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The ring homomorphism of adic completions induced by a compatible family of ring
homomorphisms between the quotients by the powers of two ideals. -/
private noncomputable def adicCompletionMap {I : Ideal A} {J : Ideal B}
    (e : ∀ n, A ⧸ I ^ n →+* B ⧸ J ^ n)
    (he : ∀ {m n} (hle : m ≤ n) (x : A ⧸ I ^ n),
      Ideal.Quotient.factorPow J hle (e n x) = e m (Ideal.Quotient.factorPow I hle x)) :
    AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J
    (fun n => (e n).comp (AdicCompletion.evalₐ I n).toRingHom) fun hle => by
      ext x
      simp [he, factorPow_evalₐ]

/-- `adicCompletionMap` is compatible with the projections. -/
private theorem evalₐ_adicCompletionMap {I : Ideal A} {J : Ideal B}
    (e : ∀ n, A ⧸ I ^ n →+* B ⧸ J ^ n)
    (he : ∀ {m n} (hle : m ≤ n) (x : A ⧸ I ^ n),
      Ideal.Quotient.factorPow J hle (e n x) = e m (Ideal.Quotient.factorPow I hle x))
    (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (adicCompletionMap e he x) = e n (AdicCompletion.evalₐ I n x) := by
  unfold adicCompletionMap
  rw [AdicCompletion.evalₐ_liftRingHom]
  · rfl
  · intro m n hle
    ext x
    simp [he, factorPow_evalₐ]

/-- `adicCompletionMap` of a family of left inverses is a left inverse. -/
private theorem adicCompletionMap_comp_eq_id {I : Ideal A} {J : Ideal B}
    {e : ∀ n, A ⧸ I ^ n →+* B ⧸ J ^ n} {f : ∀ n, B ⧸ J ^ n →+* A ⧸ I ^ n}
    (he : ∀ {m n} (hle : m ≤ n) (x : A ⧸ I ^ n),
      Ideal.Quotient.factorPow J hle (e n x) = e m (Ideal.Quotient.factorPow I hle x))
    (hf : ∀ {m n} (hle : m ≤ n) (x : B ⧸ J ^ n),
      Ideal.Quotient.factorPow I hle (f n x) = f m (Ideal.Quotient.factorPow J hle x))
    (hfe : ∀ n x, f n (e n x) = x) :
    (adicCompletionMap f hf).comp (adicCompletionMap e he) = RingHom.id _ :=
  RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => by
    simp [evalₐ_adicCompletionMap, hfe]

/-- A family of ring isomorphisms between the quotients by the powers of two ideals, compatible
with the projections, induces an isomorphism of the adic completions. -/
private noncomputable def adicCompletionEquiv {I : Ideal A} {J : Ideal B}
    (e : ∀ n, A ⧸ I ^ n ≃+* B ⧸ J ^ n)
    (he : ∀ {m n} (hle : m ≤ n) (x : A ⧸ I ^ n),
      Ideal.Quotient.factorPow J hle (e n x) = e m (Ideal.Quotient.factorPow I hle x)) :
    AdicCompletion I A ≃+* AdicCompletion J B :=
  have he' : ∀ {m n} (hle : m ≤ n) (x : B ⧸ J ^ n), Ideal.Quotient.factorPow I hle
      ((e n).symm x) = (e m).symm (Ideal.Quotient.factorPow J hle x) := fun hle x =>
    (e _).injective (by rw [RingEquiv.apply_symm_apply, ← he, RingEquiv.apply_symm_apply])
  RingEquiv.ofRingHom (adicCompletionMap (fun n => (e n).toRingHom) fun hle x => he hle x)
    (adicCompletionMap (fun n => (e n).symm.toRingHom) fun hle x => he' hle x)
    (adicCompletionMap_comp_eq_id _ _ fun n x => (e n).apply_symm_apply x)
    (adicCompletionMap_comp_eq_id _ _ fun n x => (e n).symm_apply_apply x)

/-- `adicCompletionEquiv` is compatible with the projections. -/
private theorem evalₐ_adicCompletionEquiv {I : Ideal A} {J : Ideal B}
    (e : ∀ n, A ⧸ I ^ n ≃+* B ⧸ J ^ n)
    (he : ∀ {m n} (hle : m ≤ n) (x : A ⧸ I ^ n),
      Ideal.Quotient.factorPow J hle (e n x) = e m (Ideal.Quotient.factorPow I hle x))
    (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (adicCompletionEquiv e he x) = e n (AdicCompletion.evalₐ I n x) :=
  evalₐ_adicCompletionMap (fun n => (e n).toRingHom) (fun hle x => he hle x) _ _

end AdicCompletionMap

section Package

variable {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

/-- A map with `𝔪_A B = 𝔪_B` sends `𝔪_A^N` into `𝔪_B^N`. -/
private theorem le_comap_maximalIdeal_pow (φ : A →+* B)
    (h1 : (maximalIdeal A).map φ = maximalIdeal B) (N : ℕ) :
    maximalIdeal A ^ N ≤ (maximalIdeal B ^ N).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, h1]

/-- The isomorphism of jets `A/𝔪_A^N ≅ B/𝔪_B^N` induced by `φ`. -/
private noncomputable def jetEquiv (φ : A →+* B)
    (h1 : (maximalIdeal A).map φ = maximalIdeal B) (h2 : ∀ b, ∃ a, b - φ a ∈ maximalIdeal B)
    (h3 : ∀ N a, φ a ∈ maximalIdeal B ^ N → a ∈ maximalIdeal A ^ N) (N : ℕ) :
    A ⧸ maximalIdeal A ^ N ≃+* B ⧸ maximalIdeal B ^ N :=
  RingEquiv.ofBijective (Ideal.quotientMap _ φ (le_comap_maximalIdeal_pow φ h1 N))
    ⟨Ideal.quotientMap_injective' fun a ha => h3 N a ha, by
      intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := exists_sub_mem_map_pow φ (maximalIdeal A) (h1 ▸ h2) N b
      rw [Ideal.map_pow, h1] at ha
      exact ⟨Ideal.Quotient.mk _ a, by
        rw [Ideal.quotientMap_mk]
        exact (Ideal.Quotient.eq.2 ha).symm⟩⟩

/-- The jet isomorphism is induced by `φ`. -/
private theorem jetEquiv_mk (φ : A →+* B)
    (h1 : (maximalIdeal A).map φ = maximalIdeal B) (h2 : ∀ b, ∃ a, b - φ a ∈ maximalIdeal B)
    (h3 : ∀ N a, φ a ∈ maximalIdeal B ^ N → a ∈ maximalIdeal A ^ N) (N : ℕ) (a : A) :
    jetEquiv φ h1 h2 h3 N (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a) := by
  change Ideal.quotientMap (maximalIdeal B ^ N) φ (le_comap_maximalIdeal_pow φ h1 N)
    (Ideal.Quotient.mk (maximalIdeal A ^ N) a) = _
  exact Ideal.quotientMap_mk

/-- A flat local homomorphism of Noetherian local rings with `𝔪_A B = 𝔪_B` preserves the Krull
dimension. -/
private theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq [Algebra A B] [Module.Flat A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim B = ringKrullDim A := by
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal A) (maximalIdeal B)
  rw [hmax, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]

/-- The jet isomorphisms are compatible with the transition maps. -/
private theorem factorPow_jetEquiv (φ : A →+* B)
    (h1 : (maximalIdeal A).map φ = maximalIdeal B) (h2 : ∀ b, ∃ a, b - φ a ∈ maximalIdeal B)
    (h3 : ∀ N a, φ a ∈ maximalIdeal B ^ N → a ∈ maximalIdeal A ^ N) {m n : ℕ} (hle : m ≤ n)
    (x : A ⧸ maximalIdeal A ^ n) :
    Ideal.Quotient.factorPow _ hle (jetEquiv φ h1 h2 h3 n x) =
      jetEquiv φ h1 h2 h3 m (Ideal.Quotient.factorPow _ hle x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [jetEquiv_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

/-- The completion of a Noetherian local ring is faithfully flat over it. -/
private theorem faithfullyFlat_adicCompletion [IsNoetherianRing B] :
    Module.FaithfullyFlat B (AdicCompletion (maximalIdeal B) B) :=
  have : Module.Flat B (AdicCompletion (maximalIdeal B) B) := AdicCompletion.flat_of_isNoetherian _
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- A local homomorphism of Noetherian local rings inducing an isomorphism of completions,
compatibly with the canonical maps, is faithfully flat. -/
private theorem faithfullyFlat_of_adicCompletion_ringEquiv [IsNoetherianRing A]
    [IsNoetherianRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (E : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B)
    (hE : ∀ a : A, E (algebraMap A _ a) = algebraMap B _ (algebraMap A B a)) :
    Module.FaithfullyFlat A B := by
  have : Module.Flat A (AdicCompletion (maximalIdeal B) B) := by
    rw [← RingHom.flat_algebraMap_iff, show algebraMap A (AdicCompletion (maximalIdeal B) B) =
      E.toRingHom.comp (algebraMap A _) from RingHom.ext fun a => (hE a).symm]
    exact RingHom.Flat.comp
      (RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _))
      (RingHom.Flat.of_bijective E.bijective)
  have := faithfullyFlat_adicCompletion (B := B)
  have : Module.Flat A B := flat_of_flat_of_faithfullyFlat (C := AdicCompletion (maximalIdeal B) B)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- A map with `𝔪_A B = 𝔪_B`, surjective on residue fields, recovers every ideal containing a
power of `𝔪_B` from its contraction. -/
private theorem map_comap_eq_of_maximalIdeal_pow_le (φ : A →+* B)
    (h1 : (maximalIdeal A).map φ = maximalIdeal B) (h2 : ∀ b, ∃ a, b - φ a ∈ maximalIdeal B)
    {N : ℕ} {J : Ideal B} (hJ : maximalIdeal B ^ N ≤ J) : (J.comap φ).map φ = J := by
  refine le_antisymm Ideal.map_comap_le fun b hb => ?_
  obtain ⟨a, ha⟩ := exists_sub_mem_map_pow φ (maximalIdeal A) (h1 ▸ h2) N b
  have h' : b - φ a ∈ (J.comap φ).map φ :=
    Ideal.map_mono ((le_comap_maximalIdeal_pow φ h1 N).trans (Ideal.comap_mono hJ)) ha
  have haJ : a ∈ J.comap φ := by
    rw [Ideal.map_pow, h1] at ha
    simpa using J.sub_mem hb (hJ ha)
  simpa using Ideal.add_mem _ h' (Ideal.mem_map_of_mem φ haJ)

/-- A local homomorphism `φ : A → B` of Noetherian local rings with `𝔪_A B = 𝔪_B`, surjective on
residue fields and with `φ⁻¹(𝔪_B^N) ⊆ 𝔪_A^N` for every `N`, is faithfully flat, an isomorphism on
jets and completions, and preserves dimension, embedding dimension, ideals containing a power of
the maximal ideal and, when `Â` is a normal domain, normality. -/
private theorem faithfullyFlat_and_jetEquiv_of_comap_maximalIdeal_pow [IsNoetherianRing A]
    [IsNoetherianRing B] (φ : A →+* B)
    (h1 : (maximalIdeal A).map φ = maximalIdeal B) (h2 : ∀ b, ∃ a, b - φ a ∈ maximalIdeal B)
    (h3 : ∀ N a, φ a ∈ maximalIdeal B ^ N → a ∈ maximalIdeal A ^ N)
    (hnorm : IsIntegrallyClosed A → IsDomain (AdicCompletion (maximalIdeal A) A) ∧
      IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A)) :
    φ.FaithfullyFlat ∧
      (∀ N : ℕ, ∃ e : A ⧸ maximalIdeal A ^ N ≃+* B ⧸ maximalIdeal B ^ N,
        ∀ a : A, e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a)) ∧
      ringKrullDim A = ringKrullDim B ∧
      (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank ∧
      (∃ e : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B,
        ∀ a : A, e (algebraMap A _ a) = algebraMap B _ (φ a)) ∧
      (∀ N : ℕ, (∀ I : Ideal A, maximalIdeal A ^ N ≤ I → (I.map φ).comap φ = I) ∧
        ∀ J : Ideal B, maximalIdeal B ^ N ≤ J → (J.comap φ).map φ = J) ∧
      (IsIntegrallyClosed A → IsDomain B ∧ IsIntegrallyClosed B) := by
  let e := jetEquiv φ h1 h2 h3
  let E := adicCompletionEquiv e fun hle x => factorPow_jetEquiv φ h1 h2 h3 hle x
  have hE : ∀ a : A, E (algebraMap A _ a) = algebraMap B _ (φ a) := fun a =>
    AdicCompletion.ext_evalₐ fun n => by
      rw [evalₐ_adicCompletionEquiv]
      simp [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, e, jetEquiv_mk]
  let : Algebra A B := φ.toAlgebra
  have : IsLocalHom (algebraMap A B) := ((IsLocalRing.local_hom_TFAE φ).out 3 1).1 h1.le
  have hff : Module.FaithfullyFlat A B := faithfullyFlat_of_adicCompletion_ringEquiv E hE
  refine ⟨RingHom.faithfullyFlat_algebraMap_iff.2 hff, fun N => ⟨e N, jetEquiv_mk φ h1 h2 h3 N⟩,
    (ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq h1).symm, ?_, ⟨E, hE⟩,
    fun N => ⟨fun I _ => Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I,
      fun _ hJ => map_comap_eq_of_maximalIdeal_pow_le φ h1 h2 hJ⟩, ?_⟩
  · rw [← AdicCompletion.spanFinrank_maximalIdeal_eq (R := A),
      ← AdicCompletion.spanFinrank_maximalIdeal_eq (R := B),
      ← map_maximalIdeal_of_surjective E.toRingHom E.surjective]
    exact (Ideal.spanFinrank_map_eq_of_ringEquiv E _).symm
  · intro hA
    obtain ⟨hdom, hic⟩ := hnorm hA
    let : Algebra B (AdicCompletion (maximalIdeal A) A) :=
      (E.symm.toRingHom.comp (algebraMap B (AdicCompletion (maximalIdeal B) B))).toAlgebra
    have : Module.FaithfullyFlat B (AdicCompletion (maximalIdeal A) A) := by
      rw [← RingHom.faithfullyFlat_algebraMap_iff]
      exact RingHom.FaithfullyFlat.stableUnderComposition _ _
        (RingHom.faithfullyFlat_algebraMap_iff.2 faithfullyFlat_adicCompletion)
        (RingHom.FaithfullyFlat.of_bijective E.symm.bijective)
    exact isDomain_and_isIntegrallyClosed_of_faithfullyFlat B (AdicCompletion (maximalIdeal A) A)

end Package

/-- Composition with a map that is holomorphic near `q` and tends to `p`, on holomorphic germs. -/
private noncomputable def holPullbackOfEventually {n k : ℕ} {p : Fin n → ℂ} {q : Fin k → ℂ}
    (G : (Fin k → ℂ) → Fin n → ℂ) (hG : Tendsto G (𝓝 q) (𝓝 p))
    (hGd : ∀ᶠ w in 𝓝 q, DifferentiableAt ℂ G w) : holGerms p →+* holGerms q :=
  (germPullback G hG).restrict _ _ <| by
    rintro _ ⟨f, rfl, hf⟩
    exact ⟨f ∘ G, rfl, ((hG.eventually hf).and hGd).mono fun w hw => hw.1.comp w hw.2⟩

/-- A holomorphic germ map carrying `I` into `J` induces a homomorphism `ℂ{z}/I → ℂ{w}/J`. -/
private theorem exists_ringHom_of_germMap {n k : ℕ} (p : Fin n → ℂ) (q : Fin k → ℂ)
    (I : Ideal (holGerms p)) (J : Ideal (holGerms q)) (G : (Fin k → ℂ) → Fin n → ℂ)
    (hG : Tendsto G (𝓝 q) (𝓝 p)) (hGd : ∀ᶠ w in 𝓝 q, DifferentiableAt ℂ G w)
    (hIJ : ∀ (g : holGerms p) (g' : holGerms q), (g' : Germ (𝓝 q) ℂ) = germPullback G hG g →
      g ∈ I → g' ∈ J) :
    ∃ ψ : holGerms p ⧸ I →+* holGerms q ⧸ J,
      ∀ (g : holGerms p) (g' : holGerms q), (g' : Germ (𝓝 q) ℂ) = germPullback G hG g →
        ψ (Ideal.Quotient.mk I g) = Ideal.Quotient.mk J g' := by
  let P := holPullbackOfEventually G hG hGd
  refine ⟨Ideal.Quotient.lift I ((Ideal.Quotient.mk J).comp P) fun g hg => ?_, fun g g' hg' => ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.2 (hIJ g (P g) rfl hg)
  · rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
    exact congrArg _ (Subtype.ext hg'.symm)

/-- In a Noetherian local ring, an element of `𝔪 \ 𝔪²` is part of a generating set of `𝔪` of
size `spanFinrank 𝔪`. -/
private theorem exists_span_insert_eq_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {g : R} (hg : g ∈ maximalIdeal R) (hg2 : g ∉ maximalIdeal R ^ 2) :
    ∃ s : Set R, s.Finite ∧ s.ncard + 1 ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span (insert g s) = maximalIdeal R := by
  set m := maximalIdeal R
  set v : CotangentSpace R := m.toCotangent ⟨g, hg⟩
  have hv : v ≠ 0 := by
    simpa [v, Ideal.toCotangent_eq_zero] using hg2
  have hli : LinearIndepOn (ResidueField R) id ({v} : Set (CotangentSpace R)) :=
    (linearIndepOn_singleton_iff _).2 hv
  set E := hli.extend (Set.subset_univ _)
  have hvE : v ∈ E := Module.Basis.subset_extend hli rfl
  let B := Module.Basis.extend hli
  have hEf : E.Finite := by
    have : Finite E := Module.Finite.finite_basis B
    exact Set.toFinite E
  have hcard : E.ncard = m.spanFinrank := by
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, Module.finrank_eq_nat_card_basis B,
      Nat.card_coe_set_eq]
  have hspanE : Submodule.span (ResidueField R) E = ⊤ := by
    have := B.span_eq
    rwa [Module.Basis.range_extend] at this
  choose ℓ hℓ using m.toCotangent_surjective
  let T : Set m := insert ⟨g, hg⟩ (ℓ '' (E \ {v}))
  have hT : m.toCotangent '' T = E := by
    simp only [T, Set.image_insert_eq, Set.image_image, hℓ, Set.image_id']
    exact Set.insert_sdiff_singleton.trans (Set.insert_eq_of_mem hvE)
  have hspanT : Submodule.span R T = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff, hT, hspanE]
  refine ⟨Subtype.val '' (ℓ '' (E \ {v})), ((hEf.sdiff).image _).image _, ?_, ?_⟩
  · calc (Subtype.val '' (ℓ '' (E \ {v}))).ncard + 1 ≤ (E \ {v}).ncard + 1 := by
          gcongr
          exact (Set.ncard_image_le ((hEf.sdiff).image _)).trans
            (Set.ncard_image_le hEf.sdiff)
      _ = E.ncard := Set.ncard_sdiff_singleton_add_one hvE hEf
      _ = _ := hcard
  · have := congrArg (Submodule.map m.subtype) hspanT
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
    simpa [T, Set.image_insert_eq] using this

/-- A surjection of local rings, with `R` Noetherian, between maximal ideals of the same span rank
is injective on cotangent spaces. -/
private theorem mem_maximalIdeal_sq_of_surjective {R S : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing S] [IsLocalRing S] (f : R →+* S) (hf : Function.Surjective f)
    (hrk : (maximalIdeal S).spanFinrank = (maximalIdeal R).spanFinrank) {g : R}
    (hg : g ∈ maximalIdeal R) (hfg : f g ∈ maximalIdeal S ^ 2) : g ∈ maximalIdeal R ^ 2 := by
  by_contra hg2
  obtain ⟨s, hs, hcard, hspan⟩ := exists_span_insert_eq_maximalIdeal hg hg2
  have := isNoetherianRing_of_surjective R S f hf
  set J : Ideal S := Ideal.span (f '' s)
  have hmS : maximalIdeal S = Ideal.span (insert (f g) (f '' s)) := by
    rw [← map_maximalIdeal_of_surjective f hf, ← hspan, Ideal.map_span, Set.image_insert_eq]
  have hJ : J = maximalIdeal S := by
    refine le_antisymm (hmS ▸ Ideal.span_mono (Set.subset_insert _ _)) ?_
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (maximalIdeal S).fg_of_isNoetherianRing
      (jacobson_eq_maximalIdeal _ bot_ne_top).ge ?_
    conv_lhs => rw [hmS]
    rw [Ideal.span_insert, smul_eq_mul, ← pow_two, sup_comm]
    exact sup_le_sup_left (Ideal.span_le.2 (by simpa using hfg)) _
  have h1 : (maximalIdeal S).spanFinrank ≤ s.ncard := by
    rw [← hJ]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (hs.image f)).trans
      (Set.ncard_image_le hs)
  omega

/-- Translation by `p` identifies the holomorphic germs at `p` with those at the origin. -/
private noncomputable def holGermsTranslate {m : ℕ} (p : Fin m → ℂ) :
    holGerms p ≃+* holGerms (0 : Fin m → ℂ) :=
  have h1 : Tendsto (fun z : Fin m → ℂ => z + p) (𝓝 0) (𝓝 p) := by
    simpa using (Continuous.tendsto (f := fun z : Fin m → ℂ => z + p) (by fun_prop) 0)
  have h2 : Tendsto (fun z : Fin m → ℂ => z - p) (𝓝 p) (𝓝 0) := by
    simpa using (Continuous.tendsto (f := fun z : Fin m → ℂ => z - p) (by fun_prop) p)
  RingEquiv.ofRingHom (holPullback _ (by fun_prop) h1) (holPullback _ (by fun_prop) h2)
    (by
      ext ⟨_, f, rfl, -⟩
      simp only [RingHom.coe_comp, Function.comp_apply, coe_holPullback, RingHom.id_apply]
      exact congrArg (fun F : (Fin m → ℂ) → ℂ => (F : Germ (𝓝 (0 : Fin m → ℂ)) ℂ))
        (funext fun z => by simp))
    (by
      ext ⟨_, f, rfl, -⟩
      simp only [RingHom.coe_comp, Function.comp_apply, coe_holPullback, RingHom.id_apply]
      exact congrArg (fun F : (Fin m → ℂ) → ℂ => (F : Germ (𝓝 p) ℂ)) (funext fun z => by simp))

/-- `ℂ{z₁, …, zₘ}` at any base point is regular local and factorial, and a surjection onto a local
ring of embedding dimension `m` is injective on cotangent spaces. -/
private theorem exists_isRegularLocalRing_holGerms {m : ℕ} (p : Fin m → ℂ) :
    ∃ _ : IsRegularLocalRing (holGerms p),
      ∃ _ : IsDomain (holGerms p), UniqueFactorizationMonoid (holGerms p) ∧
      ∀ (S : Type u) [CommRing S] [IsLocalRing S] (f : holGerms p →+* S),
        Function.Surjective f → (maximalIdeal S).spanFinrank = m →
        ∀ g ∈ maximalIdeal (holGerms p), f g ∈ maximalIdeal S ^ 2 →
          g ∈ maximalIdeal (holGerms p) ^ 2 := by
  obtain ⟨hreg0, hdim0, -, -⟩ := isRegularLocalRing_holGerms m
  let e := holGermsTranslate p
  have hreg : IsRegularLocalRing (holGerms p) := IsRegularLocalRing.of_ringEquiv e.symm
  have hdom : IsDomain (holGerms p) := IsRegularLocalRing.isDomain _
  refine ⟨hreg, hdom, IsRegularLocalRing.uniqueFactorizationMonoid _, ?_⟩
  intro S _ _ f hf hS g hg hfg
  refine mem_maximalIdeal_sq_of_surjective f hf ?_ hg hfg
  have h := hreg.spanFinrank_maximalIdeal
  rw [← ringKrullDim_eq_of_ringEquiv e.symm, hdim0] at h
  rw [hS]
  exact_mod_cast h.symm

/-- A holomorphic germ vanishing at the base point lies in the maximal ideal. -/
private theorem mem_maximalIdeal_holGerms_of_value_eq_zero {k : ℕ} {q : Fin k → ℂ}
    [IsLocalRing (holGerms q)] {t : holGerms q} (ht : (t : Germ (𝓝 q) ℂ).value = 0) :
    t ∈ maximalIdeal (holGerms q) := by
  intro hu
  have := hu.map ((Germ.valueRingHom (x := q)).comp (holGerms q).subtype)
  have h0 : Germ.valueRingHom (t : Germ (𝓝 q) ℂ) = 0 := ht
  simp only [RingHom.coe_comp, Function.comp_apply, Subring.coe_subtype, h0] at this
  exact not_isUnit_zero this

/-- The image in a proper quotient of a holomorphic germ vanishing at the base point lies in the
maximal ideal. -/
private theorem mk_mem_maximalIdeal_of_value_eq_zero {k : ℕ} {q : Fin k → ℂ}
    [IsLocalRing (holGerms q)] {J : Ideal (holGerms q)} [IsLocalRing (holGerms q ⧸ J)]
    (hJ : J ≠ ⊤) {t : holGerms q} (ht : (t : Germ (𝓝 q) ℂ).value = 0) :
    Ideal.Quotient.mk J t ∈ maximalIdeal (holGerms q ⧸ J) := by
  rintro ⟨u, hu⟩
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (u⁻¹ : (holGerms q ⧸ J)ˣ).1
  have h1 : t * v - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, ← hu]
    simp
  have hm := mem_maximalIdeal_holGerms_of_value_eq_zero ht
  have h2 : (1 : holGerms q) ∈ maximalIdeal (holGerms q) := by
    simpa using (maximalIdeal (holGerms q)).sub_mem ((maximalIdeal _).mul_mem_right v hm)
      (IsLocalRing.le_maximalIdeal hJ h1)
  exact (maximalIdeal.isMaximal (holGerms q)).ne_top ((Ideal.eq_top_iff_one _).2 h2)

/-! ### Taylor approximation of holomorphic germs -/

/-- A power series in the `k`-th power of the ideal of series without constant term has order at
least `k`. -/
private theorem le_order_of_mem_ker_constantCoeff_pow {σ R : Type*} [CommRing R] {N : ℕ}
    {f : MvPowerSeries σ R}
    (hf : f ∈ RingHom.ker (MvPowerSeries.constantCoeff (σ := σ) (R := R)) ^ N) :
    (N : ℕ∞) ≤ f.order := by
  induction N generalizing f with
  | zero => simp
  | succ N ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · refine le_trans ?_ MvPowerSeries.le_order_mul
      push_cast
      exact add_le_add (ih hx) (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 hy)
    · exact (le_min hx hy).trans MvPowerSeries.min_order_le_add

section Taylor

variable {n : ℕ}

/-- Substituting `zᵢ + vᵢ` for `zᵢ` and evaluating at `z` is evaluating at `z + v`. -/
private theorem eval_aeval_X_add_C (v z : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.eval z (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (v i)) q) =
      MvPolynomial.eval (z + v) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | mul_X a i ha =>
    rw [map_mul, map_mul, ha, map_mul, MvPolynomial.aeval_X]
    simp

/-- Substituting `zᵢ - vᵢ` for `zᵢ` and evaluating at `z` is evaluating at `z - v`. -/
private theorem eval_aeval_X_sub_C (v z : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.eval z (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (v i)) q) =
      MvPolynomial.eval (z - v) q := by
  simpa [sub_eq_add_neg] using eval_aeval_X_add_C (-v) z q

/-- Translation to the origin of the germ of a polynomial. -/
private theorem holGermsTranslate_polyGermHom (p : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) :
    holGermsTranslate p (polyGermHom p q) =
      polyGermHom 0 (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (p i)) q) := by
  apply Subtype.ext
  change ((((fun z => MvPolynomial.eval z q) ∘ (fun z : Fin n → ℂ => z + p) : _ → ℂ)) :
    Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = _
  rw [coe_polyGermHom]
  congr 1 with z
  exact (eval_aeval_X_add_C p z q).symm

/-- Translation from the origin of the germ of a polynomial. -/
private theorem holGermsTranslate_symm_polyGermHom (p : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) :
    (holGermsTranslate p).symm (polyGermHom 0 q) =
      polyGermHom p (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (p i)) q) := by
  apply Subtype.ext
  change ((((fun z => MvPolynomial.eval z q) ∘ (fun z : Fin n → ℂ => z - p) : _ → ℂ)) :
    Germ (𝓝 p) ℂ) = _
  rw [coe_polyGermHom]
  congr 1 with z
  exact (eval_aeval_X_sub_C p z q).symm

/-- The value at `p` of the germ of a polynomial. -/
private theorem value_polyGermHom (p : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) :
    (polyGermHom p q : Germ (𝓝 p) ℂ).value = MvPolynomial.eval p q := by
  rw [coe_polyGermHom, Germ.value_ofFun]

/-- The maximal ideal of `ℂ{z - p}` is generated by the polynomials vanishing at `p`. -/
private theorem maximalIdeal_holGerms_eq_map (p : Fin n → ℂ) [IsLocalRing (holGerms p)] :
    maximalIdeal (holGerms p) = (RingHom.ker (MvPolynomial.eval p)).map (polyGermHom p) := by
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.2 fun q hq =>
    mem_maximalIdeal_holGerms_of_value_eq_zero (by rwa [value_polyGermHom]))
  obtain ⟨_, -, hm0, -⟩ := isRegularLocalRing_holGerms n
  rw [← map_maximalIdeal_of_surjective (holGermsTranslate p).symm.toRingHom
    (holGermsTranslate p).symm.surjective, hm0, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  change (holGermsTranslate p).symm (polyGermHom 0 (MvPolynomial.X i)) ∈ _
  rw [holGermsTranslate_symm_polyGermHom]
  exact Ideal.mem_map_of_mem _ (by simp)

/-- Every holomorphic germ at `p` is congruent to a constant modulo the maximal ideal. -/
private theorem exists_sub_polyGermHom_mem_maximalIdeal (p : Fin n → ℂ)
    [IsLocalRing (holGerms p)] (r : holGerms p) :
    ∃ q, r - polyGermHom p q ∈ maximalIdeal (holGerms p) := by
  refine ⟨MvPolynomial.C (r : Germ (𝓝 p) ℂ).value,
    mem_maximalIdeal_holGerms_of_value_eq_zero ?_⟩
  change Germ.valueRingHom ((r : Germ (𝓝 p) ℂ) - (polyGermHom p _ : Germ (𝓝 p) ℂ)) = 0
  rw [map_sub]
  change (r : Germ (𝓝 p) ℂ).value - (polyGermHom p _ : Germ (𝓝 p) ℂ).value = 0
  rw [value_polyGermHom, MvPolynomial.eval_C, sub_self]

/-- A polynomial whose germ at `p` lies in the `N`-th power of the maximal ideal of `ℂ{z - p}`
lies in the `N`-th power of the ideal of polynomials vanishing at `p`. -/
private theorem mem_ker_eval_pow_of_polyGermHom_mem (p : Fin n → ℂ) [IsLocalRing (holGerms p)]
    {N : ℕ} {q : MvPolynomial (Fin n) ℂ} (hq : polyGermHom p q ∈ maximalIdeal (holGerms p) ^ N) :
    q ∈ RingHom.ker (MvPolynomial.eval p) ^ N := by
  obtain ⟨_, -, -, e0, he0⟩ := isRegularLocalRing_holGerms n
  set σ := MvPolynomial.aeval (R := ℂ) (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C (p i))
  set σ' := MvPolynomial.aeval (R := ℂ) (fun i : Fin n => MvPolynomial.X i - MvPolynomial.C (p i))
  let ρ : holGerms p →+* MvPowerSeries (Fin n) ℂ :=
    e0.toRingHom.comp ((algebraMap _ _).comp (holGermsTranslate p).toRingHom)
  have hρ : ∀ q, ρ (polyGermHom p q) = ((σ q : MvPolynomial (Fin n) ℂ) : MvPowerSeries (Fin n) ℂ) :=
    fun q => by
      change e0 (algebraMap _ _ (holGermsTranslate p (polyGermHom p q))) = _
      rw [holGermsTranslate_polyGermHom, he0]
  have hσ0 : ∀ q, MvPolynomial.eval 0 (σ q) = MvPolynomial.eval p q := fun q => by
    rw [eval_aeval_X_add_C, zero_add]
  have hmax : (maximalIdeal (holGerms p)).map ρ ≤
      RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin n) (R := ℂ)) := by
    rw [maximalIdeal_holGerms_eq_map, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.comp_apply, hρ, RingHom.mem_ker,
      ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      ← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero, hσ0]
    exact hq
  have h1 : ((σ q : MvPolynomial (Fin n) ℂ) : MvPowerSeries (Fin n) ℂ) ∈
      RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin n) (R := ℂ)) ^ N := by
    rw [← hρ]
    exact Ideal.pow_right_mono hmax N (Ideal.map_pow ρ _ _ ▸ Ideal.mem_map_of_mem ρ hq)
  have h2 : σ q ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ N := by
    refine (MvPolynomial.mem_pow_idealOfVars_iff' N _).2 fun d hd => ?_
    have := MvPowerSeries.coeff_of_lt_order (f := ((σ q : MvPolynomial (Fin n) ℂ) :
      MvPowerSeries (Fin n) ℂ)) (d := d)
      (lt_of_lt_of_le (by exact_mod_cast hd) (le_order_of_mem_ker_constantCoeff_pow h1))
    rwa [MvPolynomial.coeff_coe] at this
  have hσσ : σ' (σ q) = q := by
    rw [← AlgHom.comp_apply]
    conv_rhs => rw [← AlgHom.id_apply (R := ℂ) q]
    congr 1
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [σ, σ']
  rw [← hσσ]
  refine Ideal.pow_right_mono ?_ N (Ideal.map_pow σ'.toRingHom _ _ ▸
    Ideal.mem_map_of_mem σ'.toRingHom h2)
  rw [MvPolynomial.idealOfVars, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  simp [σ']

end Taylor

/-- An element of an extended ideal is, modulo an ideal `K` through which every element is
congruent to an image, congruent to the image of an element of the ideal. -/
private theorem exists_mem_sub_mem_of_mem_map {P R : Type*} [CommRing P] [CommRing R]
    (f : P →+* R) (I : Ideal P) (K : Ideal R) (hK : ∀ r, ∃ a, r - f a ∈ K) {x : R}
    (hx : x ∈ I.map f) : ∃ g ∈ I, x - f g ∈ K := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g, hg, by simp⟩
  | zero => exact ⟨0, I.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨g, hg, h⟩ := hx
    obtain ⟨g', hg', h'⟩ := hy
    exact ⟨g + g', I.add_mem hg hg', by
      convert K.add_mem h h' using 1
      rw [map_add]
      ring⟩
  | smul s y _ hy =>
    obtain ⟨g, hg, h⟩ := hy
    obtain ⟨c, hc⟩ := hK s
    exact ⟨c * g, I.mul_mem_left c hg, by
      convert K.add_mem (K.mul_mem_right y hc) (K.mul_mem_left (f c) h) using 1
      rw [smul_eq_mul, map_mul]
      ring⟩

/-- A polynomial whose germ at `p` lies in `𝔪^N + I 𝒪_{ℂⁿ,p}` lies in `𝔪_p^N + I`, where `𝔪_p` is
the ideal of polynomials vanishing at `p`. -/
private theorem mem_sup_of_polyGermHom_mem_sup {n : ℕ} (p : Fin n → ℂ)
    [IsLocalRing (holGerms p)] (I : Ideal (MvPolynomial (Fin n) ℂ)) {N : ℕ}
    {q : MvPolynomial (Fin n) ℂ}
    (hq : polyGermHom p q ∈ maximalIdeal (holGerms p) ^ N ⊔ I.map (polyGermHom p)) :
    q ∈ RingHom.ker (MvPolynomial.eval p) ^ N ⊔ I := by
  obtain ⟨h, hh, t, ht, hht⟩ := Submodule.mem_sup.1 hq
  have hT : ∀ r, ∃ a, r - polyGermHom p a ∈ maximalIdeal (holGerms p) ^ N := by
    intro r
    have := exists_sub_mem_map_pow (polyGermHom p) (RingHom.ker (MvPolynomial.eval p))
      (by rw [← maximalIdeal_holGerms_eq_map]; exact exists_sub_polyGermHom_mem_maximalIdeal p) N r
    rwa [Ideal.map_pow, ← maximalIdeal_holGerms_eq_map] at this
  obtain ⟨g, hg, hgt⟩ := exists_mem_sub_mem_of_mem_map _ I _ hT ht
  have hqg : polyGermHom p (q - g) ∈ maximalIdeal (holGerms p) ^ N := by
    rw [map_sub, ← hht]
    convert Ideal.add_mem _ hh hgt using 1
    ring
  simpa using Submodule.add_mem_sup (mem_ker_eval_pow_of_polyGermHom_mem p hqg) hg

/-- The prime ideal of a `ℂ`-point of an affine chart is the kernel of evaluation at it. -/
private theorem primeIdealOf_eq_ker_evalHom {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U) :
    (c.isAffineOpen.primeIdealOf ⟨y.1.toScheme, ComplexPoints.mem_chart_iff.1 y.2⟩).asIdeal =
      RingHom.ker (ComplexPoints.evalHom c.U y) := by
  have hsurj : Function.Surjective (ComplexPoints.evalHom c.U y) := fun a =>
    ⟨ComplexPoints.baseRingHom sX c.U a, ComplexPoints.evalHom_baseRingHom c.U y a⟩
  have hle : RingHom.ker (ComplexPoints.evalHom c.U y) ≤
      (c.isAffineOpen.primeIdealOf ⟨y.1.toScheme, ComplexPoints.mem_chart_iff.1 y.2⟩).asIdeal :=
    fun a ha => by
      by_contra h
      exact ComplexPoints.evalHom_ne_zero_of_notMem c.isAffineOpen y a h ha
  exact ((RingHom.ker_isMaximal_of_surjective _ hsurj).eq_of_le
    (Ideal.IsPrime.ne_top inferInstance) hle).symm

/-- A polynomial presents a section in the prime ideal of a `ℂ`-point of a chart iff it vanishes
at the coordinates of the point. -/
private theorem pres_mem_primeIdealOf_iff {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U) (q : MvPolynomial (Fin c.n) ℂ) :
    c.pres q ∈
        (c.isAffineOpen.primeIdealOf ⟨y.1.toScheme, ComplexPoints.mem_chart_iff.1 y.2⟩).asIdeal ↔
      MvPolynomial.eval (c.coords y) q = 0 := by
  rw [primeIdealOf_eq_ker_evalHom, RingHom.mem_ker, c.evalHom_pres]

/-- The relations of a chart generate a proper ideal of the germs at the coordinates of a
`ℂ`-point. -/
private theorem map_ideal_polyGermHom_ne_top {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} (c : Chart sX)
    (y : ComplexPoints.chart (sX := sX) c.U) [IsLocalRing (holGerms (c.coords y))] :
    c.ideal.map (polyGermHom (c.coords y)) ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top <| Ideal.map_le_iff_le_comap.2 fun q hq =>
    mem_maximalIdeal_holGerms_of_value_eq_zero (by
      rw [value_polyGermHom, ← c.evalHom_pres y, show c.pres q = 0 from hq, map_zero])

/-- **Hadamard's lemma** for holomorphic germs: a germ at `p` is its value at `p` plus a
combination of the coordinate germs `zᵢ - pᵢ` with holomorphic coefficients. -/
private theorem exists_eq_C_add_sum_mul {n : ℕ} (p : Fin n → ℂ) (g : holGerms p) :
    ∃ K : Fin n → holGerms p, g = polyGermHom p (MvPolynomial.C (g : Germ (𝓝 p) ℂ).value) +
      ∑ i, polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i)) * K i := by
  obtain ⟨_, h, rfl, hh⟩ := g
  obtain ⟨⟨H, hHd, hHid⟩, -⟩ :=
    exists_sub_eq_sum_sub_mul_and_comp_sub_comp_mem (E := Fin n → ℂ) hh
  have hT : Tendsto (fun y : Fin n → ℂ => (y, p)) (𝓝 p) (𝓝 (p, p)) :=
    (continuous_id.prodMk continuous_const).tendsto p
  let K : Fin n → holGerms p := fun i =>
    ⟨((fun y => H i (y, p) : (Fin n → ℂ) → ℂ) : Germ (𝓝 p) ℂ), coe_mem_holGerms
      ((hT.eventually (hHd i)).mono fun y hy =>
        hy.comp y (differentiableAt_id.prodMk (differentiableAt_const _)))⟩
  refine ⟨K, Subtype.ext ?_⟩
  change (h : Germ (𝓝 p) ℂ) = ((polyGermHom p (MvPolynomial.C (h p)) + ∑ i,
    polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i)) * K i : holGerms p) : Germ (𝓝 p) ℂ)
  have hfun : (fun y => h p + ∑ i, (y i - p i) * H i (y, p)) =
      (fun y => MvPolynomial.eval y (MvPolynomial.C (h p))) +
        ∑ i, (fun y => MvPolynomial.eval y (MvPolynomial.X i - MvPolynomial.C (p i))) *
          (fun y : Fin n → ℂ => H i (y, p)) :=
    funext fun y => by simp [Finset.sum_apply]
  have hR : ((polyGermHom p (MvPolynomial.C (h p)) + ∑ i,
      polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i)) * K i : holGerms p) :
      Germ (𝓝 p) ℂ) = ((fun y => h p + ∑ i, (y i - p i) * H i (y, p) :
        (Fin n → ℂ) → ℂ) : Germ (𝓝 p) ℂ) := by
    rw [hfun]
    change _ = Germ.coeRingHom (𝓝 p) (_ + _)
    rw [map_add, map_sum]
    simp only [map_mul]
    push_cast
    rfl
  rw [hR]
  refine Germ.coe_eq.2 ((hT.eventually hHid).mono fun y hy => ?_)
  simpa [sub_eq_iff_eq_add'] using hy

/-- A homomorphism `ℂ{z - p}/I → ℂ{w - q}/J`, with `J` proper and compatible with constants,
sends the coordinate `zᵢ - pᵢ` to the class of a germ vanishing at `q`. -/
private theorem apply_eq_zero_of_mk_eq_coord {n k : ℕ} {p : Fin n → ℂ} {q : Fin k → ℂ}
    [IsLocalRing (holGerms q)] {I : Ideal (holGerms p)} {J : Ideal (holGerms q)}
    [IsLocalRing (holGerms q ⧸ J)] (hJ : J ≠ ⊤) (ψ : holGerms p ⧸ I →+* holGerms q ⧸ J)
    (hψ : ∀ a : ℂ, ψ (Ideal.Quotient.mk I (polyGermHom p (MvPolynomial.C a))) =
      Ideal.Quotient.mk J (polyGermHom q (MvPolynomial.C a)))
    (i : Fin n) (s : holGerms q) (f : (Fin k → ℂ) → ℂ) (hf : (f : Germ (𝓝 q) ℂ) = s)
    (hs : Ideal.Quotient.mk J s =
      ψ (Ideal.Quotient.mk I (polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i))))) :
    f q = 0 := by
  by_contra hc
  have hu : IsUnit (polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i) -
      MvPolynomial.C (f q))) := isUnit_polyGermHom p _ (by simpa using hc)
  have hu' := hu.map (ψ.comp (Ideal.Quotient.mk I))
  rw [RingHom.comp_apply, map_sub, map_sub, ψ.map_sub, hψ] at hu'
  change IsUnit (ψ (Ideal.Quotient.mk I
    (polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i)))) - _) at hu'
  rw [← hs, ← map_sub] at hu'
  refine (mem_maximalIdeal _).1 (mk_mem_maximalIdeal_of_value_eq_zero hJ ?_) hu'
  change Germ.value ((s : Germ (𝓝 q) ℂ) - (polyGermHom q _ : Germ (𝓝 q) ℂ)) = 0
  rw [← hf, coe_polyGermHom, ← Germ.coe_sub, Germ.value_ofFun]
  simp

/-- **Krull induction** for germ maps: if a holomorphic germ map `G` pulls the coordinates
`zᵢ - pᵢ` back to germs `sᵢ` vanishing at `q` that represent their images under `ψ`, then `ψ`
agrees with the pullback along `G` modulo every power of the maximal ideal. -/
private theorem sub_mem_maximalIdeal_pow_of_germMap {n k : ℕ} {p : Fin n → ℂ} {q : Fin k → ℂ}
    [IsLocalRing (holGerms q)] {I : Ideal (holGerms p)} {J : Ideal (holGerms q)}
    [IsLocalRing (holGerms q ⧸ J)] (hJ : J ≠ ⊤) (ψ : holGerms p ⧸ I →+* holGerms q ⧸ J)
    (hψ : ∀ a : ℂ, ψ (Ideal.Quotient.mk I (polyGermHom p (MvPolynomial.C a))) =
      Ideal.Quotient.mk J (polyGermHom q (MvPolynomial.C a)))
    (G : (Fin k → ℂ) → Fin n → ℂ) (hG : Tendsto G (𝓝 q) (𝓝 p))
    (hGd : ∀ᶠ w in 𝓝 q, DifferentiableAt ℂ G w) (s : Fin n → holGerms q)
    (hs : ∀ i, Ideal.Quotient.mk J (s i) =
      ψ (Ideal.Quotient.mk I (polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i)))))
    (hs0 : ∀ i, (s i : Germ (𝓝 q) ℂ).value = 0)
    (hxG : ∀ i, germPullback G hG (polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i))) =
      (s i : Germ (𝓝 q) ℂ))
    (N : ℕ) (g : holGerms p) (g' : holGerms q) (hg' : (g' : Germ (𝓝 q) ℂ) = germPullback G hG g) :
    ψ (Ideal.Quotient.mk I g) - Ideal.Quotient.mk J g' ∈ maximalIdeal (holGerms q ⧸ J) ^ N := by
  haveI : AddMonoidHomClass (holGerms p ⧸ I →+* holGerms q ⧸ J) (holGerms p ⧸ I) (holGerms q ⧸ J) :=
    RingHomClass.toAddMonoidHomClass
  have hCG : ∀ a : ℂ, germPullback G hG (polyGermHom p (MvPolynomial.C a)) =
      (polyGermHom q (MvPolynomial.C a) : Germ (𝓝 q) ℂ) := fun a =>
    Germ.coe_eq.2 (Eventually.of_forall fun w => by simp)
  induction N generalizing g g' with
  | zero => simp
  | succ N ih =>
    obtain ⟨K, hg⟩ := exists_eq_C_add_sum_mul p g
    set c := (g : Germ (𝓝 p) ℂ).value
    let P := holPullbackOfEventually G hG hGd
    have hg'' : g' = polyGermHom q (MvPolynomial.C c) + ∑ i, s i * P (K i) := by
      rw [show g' = P g from Subtype.ext hg', hg, map_add, map_sum]
      simp only [map_mul]
      congr 1
      · exact Subtype.ext (hCG _)
      · exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (Subtype.ext (hxG i))
    rw [hg, hg'']
    simp only [map_add, map_sum, map_mul, hψ, ← hs]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← mul_sub, pow_succ']
    exact Ideal.mul_mem_mul (mk_mem_maximalIdeal_of_value_eq_zero hJ (hs0 i))
      (ih (K i) (P (K i)) rfl)

/-- Every `ℂ`-algebra homomorphism of analytic local rings `ℂ{z - p}/I → ℂ{w - q}/J` is the
pullback along a holomorphic map germ `(ℂᵏ, q) → (ℂⁿ, p)`. -/
private theorem exists_germMap_of_ringHom {n k : ℕ} (p : Fin n → ℂ) (q : Fin k → ℂ)
    (I : Ideal (holGerms p)) (J : Ideal (holGerms q)) (ψ : holGerms p ⧸ I →+* holGerms q ⧸ J)
    (hψ : ∀ a : ℂ, ψ (Ideal.Quotient.mk I (polyGermHom p (MvPolynomial.C a))) =
      Ideal.Quotient.mk J (polyGermHom q (MvPolynomial.C a))) :
    ∃ (G : (Fin k → ℂ) → Fin n → ℂ) (hG : Tendsto G (𝓝 q) (𝓝 p)),
      (∀ᶠ w in 𝓝 q, DifferentiableAt ℂ G w) ∧
      ∀ (g : holGerms p) (g' : holGerms q), (g' : Germ (𝓝 q) ℂ) = germPullback G hG g →
        ψ (Ideal.Quotient.mk I g) = Ideal.Quotient.mk J g' := by
  classical
  by_cases hJ : J = ⊤
  · subst hJ
    refine ⟨fun _ => p, tendsto_const_nhds, Eventually.of_forall fun _ => differentiableAt_const _,
      fun g g' _ => ?_⟩
    have : Subsingleton (holGerms q ⧸ (⊤ : Ideal (holGerms q))) :=
      Ideal.Quotient.subsingleton_iff.2 rfl
    exact Subsingleton.elim _ _
  obtain ⟨hregq, -, -, -⟩ := exists_isRegularLocalRing_holGerms.{0} q
  have : Nontrivial (holGerms q ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (holGerms q ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let x : Fin n → holGerms p := fun i => polyGermHom p (MvPolynomial.X i - MvPolynomial.C (p i))
  choose s hs using fun i => Ideal.Quotient.mk_surjective (I := J) (ψ (Ideal.Quotient.mk I (x i)))
  choose f hf hfd using fun i => (s i).2
  have hf0 : ∀ i, f i q = 0 := fun i =>
    apply_eq_zero_of_mk_eq_coord hJ ψ hψ i (s i) (f i) (hf i) (hs i)
  let G : (Fin k → ℂ) → Fin n → ℂ := fun w i => f i w + p i
  have hGd : ∀ᶠ w in 𝓝 q, DifferentiableAt ℂ G w :=
    (Filter.eventually_all.2 hfd).mono fun w hw => differentiableAt_pi.2 fun i => (hw i).add_const _
  have hGq : G q = p := funext fun i => by simp [G, hf0]
  have hG : Tendsto G (𝓝 q) (𝓝 p) := by
    have := hGd.self_of_nhds.continuousAt.tendsto
    rwa [hGq] at this
  have hxG : ∀ i, germPullback G hG (x i) = (s i : Germ (𝓝 q) ℂ) := by
    intro i
    rw [← hf i]
    exact Germ.coe_eq.2 (Eventually.of_forall fun w => by simp [G])
  refine ⟨G, hG, hGd, fun g g' hg' => sub_eq_zero.1 ?_⟩
  have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (holGerms q ⧸ J))
    (maximalIdeal.isMaximal _).ne_top
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
  exact fun N => sub_mem_maximalIdeal_pow_of_germMap hJ ψ hψ G hG hGd s hs
    (fun i => by
      rw [← hf i]
      exact hf0 i) hxG N g g' hg'

/-- A map `ψ : A → ℂ{z - p}/J` from a localization `A` of `R` at `P`, sending the section presented
by a polynomial to the class of its germ, maps `𝔪_A` onto the maximal ideal. -/
private theorem map_maximalIdeal_eq_of_pres {n : ℕ} {p : Fin n → ℂ} [IsLocalRing (holGerms p)]
    {R A : Type*} [CommRing R] [CommRing A] [IsLocalRing A] [Algebra R A]
    {π : MvPolynomial (Fin n) ℂ →+* R} {P : Ideal R} {J : Ideal (holGerms p)}
    [IsLocalRing (holGerms p ⧸ J)] {ψ : A →+* holGerms p ⧸ J} (hπ : Function.Surjective π)
    (hJ : J ≠ ⊤) (hmA : maximalIdeal A = P.map (algebraMap R A))
    (hP : ∀ q, π q ∈ P ↔ MvPolynomial.eval p q = 0)
    (hψ : ∀ q, ψ (algebraMap R A (π q)) = Ideal.Quotient.mk J (polyGermHom p q)) :
    (maximalIdeal A).map ψ = maximalIdeal (holGerms p ⧸ J) := by
  refine le_antisymm ?_ ?_
  · rw [hmA, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro s hs
    obtain ⟨q, rfl⟩ := hπ s
    rw [Ideal.mem_comap, RingHom.comp_apply, hψ]
    refine mk_mem_maximalIdeal_of_value_eq_zero hJ ?_
    rw [value_polyGermHom]
    exact (hP q).1 hs
  · rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective,
      maximalIdeal_holGerms_eq_map, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.comp_apply, ← hψ]
    exact Ideal.mem_map_of_mem _ (hmA ▸ Ideal.mem_map_of_mem _ ((hP q).2 hq))

/-- A map `ψ : A → ℂ{z - p}/J` sending the section presented by a polynomial to the class of its
germ is surjective on residue fields. -/
private theorem exists_sub_mem_maximalIdeal_of_pres {n : ℕ} {p : Fin n → ℂ}
    [IsLocalRing (holGerms p)] {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {π : MvPolynomial (Fin n) ℂ →+* R} {J : Ideal (holGerms p)} [IsLocalRing (holGerms p ⧸ J)]
    {ψ : A →+* holGerms p ⧸ J}
    (hψ : ∀ q, ψ (algebraMap R A (π q)) = Ideal.Quotient.mk J (polyGermHom p q))
    (b : holGerms p ⧸ J) : ∃ a, b - ψ a ∈ maximalIdeal (holGerms p ⧸ J) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) b
  obtain ⟨q, hq⟩ := exists_sub_polyGermHom_mem_maximalIdeal p r
  refine ⟨algebraMap R A (π q), ?_⟩
  rw [hψ, ← map_sub,
    ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective]
  exact Ideal.mem_map_of_mem _ hq

/-- For `R = ℂ[z]/I` with localization `A` at `P`, a map `ψ : A → ℂ{z - p}/I` sending the section
presented by a polynomial to the class of its germ satisfies `ψ⁻¹(𝔪^N) ⊆ 𝔪_A^N`. -/
private theorem mem_maximalIdeal_pow_of_pres {n : ℕ} {p : Fin n → ℂ} [IsLocalRing (holGerms p)]
    {R A : Type*} [CommRing R] [CommRing A] [IsLocalRing A] [Algebra R A]
    {π : MvPolynomial (Fin n) ℂ →+* R} {P : Ideal R} [P.IsPrime] [IsLocalization.AtPrime A P]
    {J : Ideal (holGerms p)} [IsLocalRing (holGerms p ⧸ J)] {ψ : A →+* holGerms p ⧸ J}
    (hπ : Function.Surjective π) (hmA : maximalIdeal A = P.map (algebraMap R A))
    (hP : ∀ q, π q ∈ P ↔ MvPolynomial.eval p q = 0)
    (hJ : J = (RingHom.ker π).map (polyGermHom p))
    (hψ : ∀ q, ψ (algebraMap R A (π q)) = Ideal.Quotient.mk J (polyGermHom p q))
    (N : ℕ) (a : A) (ha : ψ a ∈ maximalIdeal (holGerms p ⧸ J) ^ N) : a ∈ maximalIdeal A ^ N := by
  subst hJ
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl a
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  refine Ideal.mul_mem_right _ _ ?_
  have hs : ψ (algebraMap R A s) ∈ maximalIdeal (holGerms p ⧸ _) ^ N := by
    have := Ideal.mul_mem_right (ψ (algebraMap _ A (t : R))) _ ha
    rwa [← map_mul, IsLocalization.mk'_spec] at this
  obtain ⟨q, rfl⟩ := hπ s
  rw [hψ, ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, Ideal.mem_quotient_iff_mem_sup] at hs
  obtain ⟨u, hu, v, hv, huv⟩ :=
    Submodule.mem_sup.1 (mem_sup_of_polyGermHom_mem_sup p (RingHom.ker π) hs)
  rw [← huv, map_add, RingHom.mem_ker.1 hv, add_zero, hmA, ← Ideal.map_pow]
  refine Ideal.mem_map_of_mem _ (Ideal.pow_right_mono
    (I := (RingHom.ker (MvPolynomial.eval p)).map π) (J := P)
    (Ideal.map_le_iff_le_comap.2 fun q hq => (hP q).2 hq) N ?_)
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hu

/-- The completion of a normal local domain that is a localization of a finitely generated
`ℂ`-algebra at a prime is a normal domain. -/
private theorem isDomain_and_isIntegrallyClosed_adicCompletion {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra ℂ R] [Algebra ℂ A]
    [Algebra R A] [IsScalarTower ℂ R A] [Algebra.FiniteType ℂ R] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime A P] :
    IsDomain (AdicCompletion (maximalIdeal A) A) ∧
      IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  have : Algebra.EssFiniteType R A := Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
  have : Algebra.EssFiniteType ℂ A := Algebra.EssFiniteType.comp ℂ R A
  obtain ⟨-, -, hN⟩ := MMP.Resolution.isNormalDomain_adicCompletion_of_essFiniteType ℂ A
    (IsNormalRing.of_isIntegrallyClosed A)
  exact ⟨hN.isDomain, hN.isIntegrallyClosed⟩

/-- The conditions `𝔪_A S = 𝔪_S`, surjectivity on residue fields and `ψ⁻¹(𝔪_S^N) ⊆ 𝔪_A^N` pass
from `ψ = e ∘ φ` to `φ` along a ring isomorphism `e : B ≃ S`. -/
private theorem map_maximalIdeal_conditions_of_ringEquiv {A B S : Type*} [CommRing A]
    [CommRing B] [CommRing S] [IsLocalRing A] [IsLocalRing B] [IsLocalRing S] (φ : A →+* B)
    (ψ : A →+* S) (e : B ≃+* S) (hφψ : e.toRingHom.comp φ = ψ)
    (h1 : (maximalIdeal A).map ψ = maximalIdeal S) (h2 : ∀ b, ∃ a, b - ψ a ∈ maximalIdeal S)
    (h3 : ∀ N a, ψ a ∈ maximalIdeal S ^ N → a ∈ maximalIdeal A ^ N) :
    (maximalIdeal A).map φ = maximalIdeal B ∧ (∀ b, ∃ a, b - φ a ∈ maximalIdeal B) ∧
      ∀ N a, φ a ∈ maximalIdeal B ^ N → a ∈ maximalIdeal A ^ N := by
  have hφ : φ = e.symm.toRingHom.comp ψ := by
    rw [← hφψ, ← RingHom.comp_assoc, ← RingEquiv.toRingHom_trans', RingEquiv.self_trans_symm,
      RingEquiv.toRingHom_refl', RingHom.id_comp]
  have hmB : (maximalIdeal S).map e.symm.toRingHom = maximalIdeal B :=
    map_maximalIdeal_of_surjective _ e.symm.surjective
  have hmB' : (maximalIdeal B).map e.toRingHom = maximalIdeal S :=
    map_maximalIdeal_of_surjective _ e.surjective
  refine ⟨by rw [hφ, ← Ideal.map_map, h1, hmB], fun b => ?_, fun N a ha => h3 N a ?_⟩
  · obtain ⟨a, ha⟩ := h2 (e b)
    refine ⟨a, ?_⟩
    rw [← hmB, hφ, RingHom.comp_apply,
      show b - e.symm.toRingHom (ψ a) = e.symm.toRingHom (e b - ψ a) by simp]
    exact Ideal.mem_map_of_mem _ ha
  · have := Ideal.mem_map_of_mem e.toRingHom ha
    rwa [Ideal.map_pow, hmB', ← RingHom.comp_apply, hφψ] at this

/-- **The algebraic and the analytic local ring at a `ℂ`-point.** The stalk map
`φ : 𝒪_{X,y} → 𝒪_{X^an,y}` is a faithfully flat local map of Noetherian local rings with
`𝔪_A B = 𝔪_B`, an isomorphism on all jets, and preserving dimension, embedding dimension,
completion, ideals containing a power of the maximal ideal, and normality. -/
private theorem analyticStalk_comparison {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsVariety ℂ sX] (y : ComplexPoints sX) :
    let A := X.presheaf.stalk y.toScheme
    let B := (analytification sX).presheaf.stalk y
    let φ : A →+* B := ((analytificationHom sX).hom.stalkMap y).hom
    (∃ _ : IsLocalRing B, IsNoetherianRing B ∧ φ.FaithfullyFlat ∧
      (maximalIdeal A).map φ = maximalIdeal B ∧
      (∀ N : ℕ, ∃ e : A ⧸ maximalIdeal A ^ N ≃+* B ⧸ maximalIdeal B ^ N,
        ∀ a : A, e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a)) ∧
      ringKrullDim A = ringKrullDim B ∧
      (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank ∧
      (∃ e : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B,
        ∀ a : A, e (algebraMap A _ a) = algebraMap B _ (φ a)) ∧
      (∀ N : ℕ, (∀ I : Ideal A, maximalIdeal A ^ N ≤ I → (I.map φ).comap φ = I) ∧
        ∀ J : Ideal B, maximalIdeal B ^ N ≤ J → (J.comap φ).map φ = J) ∧
      (IsIntegrallyClosed A → IsDomain B ∧ IsIntegrallyClosed B)) := by
  intro A B φ
  obtain ⟨U, hU, hyU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top y.toScheme)
  obtain ⟨c, rfl⟩ := Chart.exists_eq (sX := sX) hU
  have hy : y ∈ ComplexPoints.chart (sX := sX) c.U := ComplexPoints.mem_chart_iff.2 hyU
  set y' : ComplexPoints.chart (sX := sX) c.U := ⟨y, hy⟩
  set p := c.coords y'
  obtain ⟨hregp, -, -, -⟩ := exists_isRegularLocalRing_holGerms.{0} p
  set J := c.ideal.map (polyGermHom p)
  have hJtop : J ≠ ⊤ := map_ideal_polyGermHom_ne_top c y'
  have : Nontrivial (holGerms p ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
  have : IsLocalRing (holGerms p ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  set P := (c.isAffineOpen.primeIdealOf
    ⟨y'.1.toScheme, ComplexPoints.mem_chart_iff.1 y'.2⟩).asIdeal
  let : Algebra Γ(X, c.U) A := TopCat.Presheaf.algebra_section_stalk X.presheaf
    ⟨y'.1.toScheme, ComplexPoints.mem_chart_iff.1 y'.2⟩
  have : IsLocalization.AtPrime A P :=
    c.isAffineOpen.isLocalization_stalk ⟨y'.1.toScheme, ComplexPoints.mem_chart_iff.1 y'.2⟩
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing P.primeCompl A
    (isNoetherianRing_of_surjective _ _ c.pres c.surjective)
  have hmA : maximalIdeal A = P.map (algebraMap Γ(X, c.U) A) :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal P A).symm
  have hPker : ∀ q, c.pres q ∈ P ↔ MvPolynomial.eval p q = 0 := pres_mem_primeIdealOf_iff c y'
  let ψ : A →+* holGerms p ⧸ J := c.stalkHom y'
  have hψpres : ∀ q, ψ (algebraMap Γ(X, c.U) A (c.pres q)) =
      Ideal.Quotient.mk J (polyGermHom p q) := fun q =>
    (c.stalkHom_germ y' (c.pres q)).trans (Chart.toStalkRing_pres c p q)
  have hnorm : IsIntegrallyClosed A → IsDomain (AdicCompletion (maximalIdeal A) A) ∧
      IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := fun _ => by
    let : Algebra ℂ Γ(X, c.U) := (ComplexPoints.baseRingHom sX c.U).toAlgebra
    let : Algebra ℂ A :=
      ((algebraMap Γ(X, c.U) A).comp (ComplexPoints.baseRingHom sX c.U)).toAlgebra
    have : IsScalarTower ℂ Γ(X, c.U) A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.FiniteType ℂ Γ(X, c.U) :=
      Algebra.FiniteType.iff_quotient_mvPolynomial''.2 ⟨c.n, MvPolynomial.aeval c.gen, c.surjective⟩
    exact isDomain_and_isIntegrallyClosed_adicCompletion P
  obtain ⟨e₀, he⟩ := Chart.exists_stalk_ringEquiv y c hy
  let e : B ≃+* holGerms p ⧸ J := e₀
  have hφψ : e.toRingHom.comp φ = ψ :=
    IsLocalization.ringHom_ext P.primeCompl (RingHom.ext fun s =>
      (he s).trans (c.stalkHom_germ y' s).symm)
  have : Nontrivial B := e.symm.injective.nontrivial
  have hBloc : IsLocalRing B := IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  have : IsNoetherianRing B := isNoetherianRing_of_ringEquiv _ e.symm
  obtain ⟨h1, h2, h3⟩ := map_maximalIdeal_conditions_of_ringEquiv φ ψ e hφψ
    (map_maximalIdeal_eq_of_pres (π := c.pres) c.surjective hJtop hmA hPker hψpres)
    (exists_sub_mem_maximalIdeal_of_pres (π := c.pres) hψpres)
    (mem_maximalIdeal_pow_of_pres (π := c.pres) c.surjective hmA hPker rfl hψpres)
  obtain ⟨hff, hrest⟩ := faithfullyFlat_and_jetEquiv_of_comap_maximalIdeal_pow φ h1 h2 h3 hnorm
  exact ⟨hBloc, inferInstance, hff, h1, hrest⟩

/-- **The algebraic and analytic local rings of a complex variety.** For a complex variety `X`
and a `ℂ`-point `y`, with `A = 𝒪_{X,y}`, `B = 𝒪_{X^an,y}` and `φ : A → B` the stalk map of
`MMP.Analytic.analytificationHom`: `B` is Noetherian local, `φ` is faithfully flat with
`𝔪_A B = 𝔪_B`, `φ` induces `A/𝔪_A^N ≅ B/𝔪_B^N` for all `N`, the two rings have the same
dimension, embedding dimension and completion, extension and contraction identify ideals
containing `𝔪^N`, normality of `A` gives that `B` is a normal domain, and `B` is the quotient
`ℂ{z - p}/I` for every chart `ℂ[z]/I` around `y`. Moreover `ℂ`-algebra homomorphisms of
analytic local rings are pullbacks along holomorphic map germs, and conversely; and
`ℂ{z₁, …, zₘ}` is regular local factorial, with a surjection onto a local ring of embedding
dimension `m` inducing an injection of cotangent spaces (surjectivity on cotangent spaces being
automatic for a surjection). -/
@[mmp "lem_mmp_complex_analytic_local_ring_package"]
public theorem analyticStalk_package {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsVariety ℂ sX] (y : ComplexPoints sX) :
    let A := X.presheaf.stalk y.toScheme
    let B := (analytification sX).presheaf.stalk y
    let φ : A →+* B := ((analytificationHom sX).hom.stalkMap y).hom
    (∃ _ : IsLocalRing B, IsNoetherianRing B ∧ φ.FaithfullyFlat ∧
      (maximalIdeal A).map φ = maximalIdeal B ∧
      (∀ N : ℕ, ∃ e : A ⧸ maximalIdeal A ^ N ≃+* B ⧸ maximalIdeal B ^ N,
        ∀ a : A, e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a)) ∧
      ringKrullDim A = ringKrullDim B ∧
      (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank ∧
      (∃ e : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B,
        ∀ a : A, e (algebraMap A _ a) = algebraMap B _ (φ a)) ∧
      (∀ N : ℕ, (∀ I : Ideal A, maximalIdeal A ^ N ≤ I → (I.map φ).comap φ = I) ∧
        ∀ J : Ideal B, maximalIdeal B ^ N ≤ J → (J.comap φ).map φ = J) ∧
      (IsIntegrallyClosed A → IsDomain B ∧ IsIntegrallyClosed B) ∧
      ∀ (c : Chart sX) (hy : y ∈ ComplexPoints.chart (sX := sX) c.U),
        ∃ e : B ≃+* c.StalkRing (c.coords ⟨y, hy⟩), ∀ f : Γ(X, c.U),
          e (φ (X.presheaf.germ c.U y.toScheme (ComplexPoints.mem_chart_iff.1 hy) f)) =
            c.toStalkRing (c.coords ⟨y, hy⟩) f) ∧
    (∀ {n k : ℕ} (p : Fin n → ℂ) (q : Fin k → ℂ) (I : Ideal (holGerms p))
        (J : Ideal (holGerms q)),
      (∀ ψ : holGerms p ⧸ I →+* holGerms q ⧸ J,
        (∀ a : ℂ, ψ (Ideal.Quotient.mk I (polyGermHom p (MvPolynomial.C a))) =
          Ideal.Quotient.mk J (polyGermHom q (MvPolynomial.C a))) →
        ∃ (G : (Fin k → ℂ) → Fin n → ℂ) (hG : Tendsto G (𝓝 q) (𝓝 p)),
          (∀ᶠ w in 𝓝 q, DifferentiableAt ℂ G w) ∧
          ∀ (g : holGerms p) (g' : holGerms q), (g' : Germ (𝓝 q) ℂ) = germPullback G hG g →
            ψ (Ideal.Quotient.mk I g) = Ideal.Quotient.mk J g') ∧
      ∀ (G : (Fin k → ℂ) → Fin n → ℂ) (hG : Tendsto G (𝓝 q) (𝓝 p)),
        (∀ᶠ w in 𝓝 q, DifferentiableAt ℂ G w) →
        (∀ (g : holGerms p) (g' : holGerms q), (g' : Germ (𝓝 q) ℂ) = germPullback G hG g →
          g ∈ I → g' ∈ J) →
        ∃ ψ : holGerms p ⧸ I →+* holGerms q ⧸ J,
          ∀ (g : holGerms p) (g' : holGerms q), (g' : Germ (𝓝 q) ℂ) = germPullback G hG g →
            ψ (Ideal.Quotient.mk I g) = Ideal.Quotient.mk J g') ∧
    ∀ {m : ℕ} (p : Fin m → ℂ), ∃ _ : IsRegularLocalRing (holGerms p),
      ∃ _ : IsDomain (holGerms p), UniqueFactorizationMonoid (holGerms p) ∧
      ∀ (S : Type u) [CommRing S] [IsLocalRing S] (f : holGerms p →+* S),
        Function.Surjective f → (maximalIdeal S).spanFinrank = m →
        ∀ g ∈ maximalIdeal (holGerms p), f g ∈ maximalIdeal S ^ 2 →
          g ∈ maximalIdeal (holGerms p) ^ 2 :=
  ⟨by
    obtain ⟨hB, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := analyticStalk_comparison sX y
    exact ⟨hB, h1, h2, h3, h4, h5, h6, h7, h8, h9, fun c hy => Chart.exists_stalk_ringEquiv y c hy⟩,
    fun p q I J => ⟨exists_germMap_of_ringHom p q I J, exists_ringHom_of_germMap p q I J⟩,
    exists_isRegularLocalRing_holGerms⟩

end MMP.Analytic

end
