module
public import MMP.RingTheory.RegularLocalRing.CompletionStrictHenselization

/-!
# Reduced plane curve germs: the Jacobian quotient and formal powers

Let `k` be a perfect field and `(R, 𝔪)` the local ring of a closed point on a smooth surface
over `k`, presented algebraically: a local `k`-algebra, essentially of finite type, with residue
field finite over `k` and a regular system of parameters `x, y`. The differentials `dx, dy` form
a basis of `Ω_{R/k}`; the dual coordinate derivations `∂_x, ∂_y` satisfy `∂(𝔪ⁿ⁺¹) ⊆ 𝔪ⁿ` and so
extend to continuous `k`-derivations of the completion `R^ = AdicCompletion 𝔪 R`.

For a nonzero `f ∈ R` with `R ⧸ (f)` reduced, the curve `f = 0` is generically smooth over `k`,
so every prime containing the Jacobian ideal `J = (f, ∂_x f, ∂_y f)` is `𝔪`. Hence `R ⧸ J` has
finite length, and so does `R^ ⧸ J R^ ≅ R ⧸ J`.

Consequently such an `f` is not a formal `m`-th power for `m ≥ 2`: if `f = z ^ m g` in `R^`
with `z ∈ 𝔪 R^`, then `f, ∂_x f, ∂_y f ∈ z ^ (m - 1) R^`, so `R^ ⧸ z ^ (m - 1) R^` would have
finite length, which Krull's height theorem forbids in the two-dimensional local ring `R^`.

## Main results

* `MMP.Resolution.exists_derivation_isFiniteLength_adicCompletion_quotient_jacobian`: the
  coordinate derivations, their continuous extensions to `R^`, and finite length of
  `R^ ⧸ (f, ∂_x f, ∂_y f)`.
* `MMP.Resolution.algebraMap_notMem_span_pow_adicCompletion`: `f ∉ z ^ m R^` for `m ≥ 2` and
  `z ∈ 𝔪 R^`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], §1.8, Lemma 1.72
-/

@[expose] public section

open IsLocalRing

namespace MMP.Resolution

section Extension

variable {k : Type*} [CommRing k] {A : Type*} [CommRing A] [Algebra k A]

/-- A derivation maps `I ^ (n + 1)` into `I ^ n`. -/
private theorem derivation_mem_pow_of_mem_pow_succ (D : Derivation k A A) (I : Ideal A) (n : ℕ) :
    ∀ a ∈ I ^ (n + 1), D a ∈ I ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun x y hx hy => ?_)
    · rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hb) ?_
      rw [pow_succ, mul_comm c]
      exact Ideal.mul_mem_mul (ih b hb) hc
    · rw [map_add]
      exact Ideal.add_mem _ hx hy

/-- A derivation is continuous for the `K`-adic topology. -/
private theorem continuous_derivation_adicTopology (δ : Derivation k A A) (K : Ideal A) :
    @Continuous _ _ K.adicTopology K.adicTopology δ := by
  letI := K.adicTopology
  rw [continuous_iff_continuousAt]
  intro x
  refine ((Ideal.hasBasis_nhds_adic K x).tendsto_iff (Ideal.hasBasis_nhds_adic K (δ x))).2
    fun n _ => ⟨n + 1, trivial, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨δ z, derivation_mem_pow_of_mem_pow_succ δ K n z hz, by simp⟩

variable (I : Ideal A)

/-- A representative in `A` of the `n`-th truncation of `x`. -/
private noncomputable def rep (x : AdicCompletion I A) (n : ℕ) : A :=
  (Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)).choose

private theorem mk_rep (x : AdicCompletion I A) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (rep I x n) = AdicCompletion.evalₐ I n x :=
  (Ideal.Quotient.mk_surjective _).choose_spec

private theorem evalₐ_eq_of_evalₐ_succ_eq {x : AdicCompletion I A} {n : ℕ} {a : A}
    (h : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk _ a) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk _ a := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, Ideal.Quotient.eq] at h ⊢
  have h1 : f.val n - f.val (n + 1) ∈ I ^ n := by
    have := SModEq.sub_mem.mp (f.property (Nat.le_succ n))
    rwa [smul_eq_mul, Ideal.mul_top] at this
  simpa using Ideal.add_mem _ h1 (Ideal.pow_le_pow_right (Nat.le_succ n) h)

variable (D : Derivation k A A)

/-- The Cauchy sequence `n ↦ D (x_{n+1})` defining the extension of `D` at `x`. -/
private noncomputable def extendSeq (x : AdicCompletion I A) :
    AdicCompletion.AdicCauchySequence I A :=
  AdicCompletion.AdicCauchySequence.mk I A (fun n => D (rep I x (n + 1))) fun n => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub]
    refine derivation_mem_pow_of_mem_pow_succ D I n _ ?_
    rw [← Ideal.Quotient.eq, mk_rep]
    exact evalₐ_eq_of_evalₐ_succ_eq I (mk_rep I x (n + 2)).symm

/-- The extension of `D` to the completion, as a function. -/
private noncomputable def extendFun (x : AdicCompletion I A) : AdicCompletion I A :=
  AdicCompletion.mk I A (extendSeq I D x)

private theorem evalₐ_extendFun {x : AdicCompletion I A} {n : ℕ} {a : A}
    (h : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk _ a) :
    AdicCompletion.evalₐ I n (extendFun I D x) = Ideal.Quotient.mk _ (D a) := by
  rw [extendFun, AdicCompletion.evalₐ_mk, Ideal.Quotient.eq]
  change D (rep I x (n + 1)) - D a ∈ I ^ n
  rw [← map_sub]
  exact derivation_mem_pow_of_mem_pow_succ D I n _ (Ideal.Quotient.eq.mp ((mk_rep I x _).trans h))

private theorem extendFun_add (x y : AdicCompletion I A) :
    extendFun I D (x + y) = extendFun I D x + extendFun I D y :=
  AdicCompletion.ext_evalₐ fun n => by
    rw [map_add, evalₐ_extendFun I D (a := rep I x (n + 1) + rep I y (n + 1))
        (by rw [map_add, map_add, mk_rep, mk_rep]),
      evalₐ_extendFun I D (mk_rep I x _).symm, evalₐ_extendFun I D (mk_rep I y _).symm,
      map_add, map_add]

private theorem extendFun_mul (x y : AdicCompletion I A) :
    extendFun I D (x * y) = x * extendFun I D y + y * extendFun I D x :=
  AdicCompletion.ext_evalₐ fun n => by
    rw [map_add, map_mul, map_mul, evalₐ_extendFun I D (a := rep I x (n + 1) * rep I y (n + 1))
        (by rw [map_mul, map_mul, mk_rep, mk_rep]),
      evalₐ_extendFun I D (mk_rep I x _).symm, evalₐ_extendFun I D (mk_rep I y _).symm,
      evalₐ_eq_of_evalₐ_succ_eq I (mk_rep I x _).symm,
      evalₐ_eq_of_evalₐ_succ_eq I (mk_rep I y _).symm, D.leibniz, smul_eq_mul, smul_eq_mul,
      map_add, map_mul, map_mul]

private theorem extendFun_of (r : A) :
    extendFun I D (AdicCompletion.of I A r) = AdicCompletion.of I A (D r) :=
  AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_extendFun I D (AdicCompletion.evalₐ_of I (n + 1) r), AdicCompletion.evalₐ_of]

/-- The extension of `D` to the `I`-adic completion. -/
private noncomputable def extendDerivation :
    Derivation k (AdicCompletion I A) (AdicCompletion I A) :=
  Derivation.mk'
    { toFun := extendFun I D
      map_add' := extendFun_add I D
      map_smul' := fun c x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, extendFun_mul,
          AdicCompletion.algebraMap_apply, extendFun_of, Derivation.map_algebraMap]
        simp }
    fun x y => by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] using extendFun_mul I D x y

private theorem extendDerivation_algebraMap (r : A) :
    extendDerivation I D (algebraMap A (AdicCompletion I A) r) =
      algebraMap A (AdicCompletion I A) (D r) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]
  exact extendFun_of I D r

end Extension

section Steps

variable (k : Type*) [Field k] [PerfectField k] {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra k R] [Algebra.EssFiniteType k R] [Module.Finite k (ResidueField R)]

local notation "R^" => AdicCompletion (maximalIdeal R) R

omit [Module.Finite k (ResidueField R)] in
/-- A regular local ring essentially of finite type over a perfect field is formally smooth. -/
private theorem formallySmooth_of_isRegularLocalRing (hreg : IsRegularLocalRing R) :
    Algebra.FormallySmooth k R := by
  let S := Algebra.EssFiniteType.subalgebra k R
  let q : Ideal S := (maximalIdeal R).comap (algebraMap S R)
  have hloc := Algebra.EssFiniteType.isLocalization k R
  have hM : Algebra.EssFiniteType.submonoid k R = q.primeCompl := by
    ext s
    simp only [Algebra.EssFiniteType.submonoid, Submonoid.mem_comap, Subalgebra.algebraMap_apply,
      Ideal.primeCompl, Ideal.coe_comap, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      Set.mem_preimage, SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff, not_not, q]
    exact Iff.rfl
  rw [hM] at hloc
  have : IsLocalization.AtPrime R q := hloc
  have : Algebra.IsSeparableExtension k q.ResidueField :=
    Algebra.isSeparableExtension_of_perfectField _ _
  have : Algebra.FormallySmooth k (Localization.AtPrime q) :=
    (Algebra.isSmoothAt_iff_isRegularLocalRing q R).2 hreg
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) R).restrictScalars k)

/-- The differentials `dx, dy` of a regular system of parameters form a basis of `Ω_{R/k}`. -/
private theorem bijective_linearCombination_D {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) :
    Function.Bijective
      (Finsupp.linearCombination R (fun i => KaehlerDifferential.D k R (![x, y] i))) := by
  have : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing k R
  have : Algebra.FormallySmooth k R :=
    formallySmooth_of_isRegularLocalRing k
      (MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hxy)
  have : Algebra.FormallyUnramified k (ResidueField R) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  obtain ⟨ht0, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular _ hxy.1 hxy.2
  have : Module.Projective R Ω[R⁄k] := ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  apply Module.IsLocalRing.linearCombination_bijective_of_flat
  refine ⟨MMP.Flips.ResolutionInputs.linearIndependent_tmul_D k _ ht0 hli, ?_⟩
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  exact top_le_iff.mp (MMP.Flips.ResolutionInputs.span_tmul_D k _ hxy.1)

/-- The coordinate derivations dual to the basis `dx, dy` of `Ω_{R/k}`. -/
private theorem exists_coordinate_derivations {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) :
    ∃ Dx Dy : Derivation k R R, Dx x = 1 ∧ Dx y = 0 ∧ Dy x = 0 ∧ Dy y = 1 := by
  have h := bijective_linearCombination_D k hxy
  let b := MMP.Flips.ResolutionInputs.basisOfBijective _ h
  have hb := MMP.Flips.ResolutionInputs.basisOfBijective_apply _ h
  have key : ∀ i j, b.coord i (KaehlerDifferential.D k R (![x, y] j)) = Finsupp.single j 1 i :=
    fun i j => by rw [← hb j, b.coord_apply, b.repr_self]
  exact ⟨(b.coord 0).compDer (KaehlerDifferential.D k R),
    (b.coord 1).compDer (KaehlerDifferential.D k R), by simpa using key 0 0, by simpa using key 0 1,
    by simpa using key 1 0, by simpa using key 1 1⟩

/-- `df = Dx f · dx + Dy f · dy` in `Ω_{R/k}`. -/
private theorem D_eq_add {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (Dx Dy : Derivation k R R) (h1 : Dx x = 1) (h2 : Dx y = 0) (h3 : Dy x = 0) (h4 : Dy y = 1)
    (f : R) :
    KaehlerDifferential.D k R f =
      Dx f • KaehlerDifferential.D k R x + Dy f • KaehlerDifferential.D k R y := by
  obtain ⟨c, hc⟩ := (bijective_linearCombination_D k hxy).2 (KaehlerDifferential.D k R f)
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
    at hc
  have e : ∀ D : Derivation k R R, D f = c 0 * D x + c 1 * D y := fun D => by
    rw [← Derivation.liftKaehlerDifferential_comp_D D f, ← hc]
    simp [Derivation.liftKaehlerDifferential_comp_D]
  rw [e Dx, e Dy, h1, h2, h3, h4, ← hc]
  simp

/-- If `Dx f, Dy f ∈ P` and `f ∈ P`, then `f` lies in the square of the maximal ideal of `R_P`. -/
private theorem algebraMap_mem_maximalIdeal_sq {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    (Dx Dy : Derivation k R R) (h1 : Dx x = 1) (h2 : Dx y = 0) (h3 : Dy x = 0) (h4 : Dy y = 1)
    (P : Ideal R) [P.IsPrime] (f : R) (hf : f ∈ P) (hfx : Dx f ∈ P) (hfy : Dy f ∈ P) :
    algebraMap R (Localization.AtPrime P) f ∈ maximalIdeal (Localization.AtPrime P) ^ 2 := by
  have : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing k R
  have : Algebra.FormallySmooth k R := formallySmooth_of_isRegularLocalRing k
    (MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hxy)
  set L := Localization.AtPrime P
  have : Algebra.FormallySmooth R L := Algebra.FormallySmooth.of_isLocalization P.primeCompl
  have : Algebra.FormallySmooth k L := Algebra.FormallySmooth.comp k R L
  have : Algebra.EssFiniteType R L := Algebra.EssFiniteType.of_isLocalization L P.primeCompl
  have : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k R L
  have : Algebra.EssFiniteType k (ResidueField L) :=
    Algebra.EssFiniteType.comp k L (ResidueField L)
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := k) (P := L)
    (A := ResidueField L) residue_surjective).mpr inferInstance
  have hmax : ∀ r ∈ P, algebraMap L (ResidueField L) (algebraMap R L r) = 0 := fun r hr =>
    (residue_eq_zero_iff _).mpr (by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hr)
  have hm : algebraMap R L f ∈ RingHom.ker (algebraMap L (ResidueField L)) := hmax f hf
  have key : KaehlerDifferential.kerCotangentToTensor k L (ResidueField L)
      ((RingHom.ker (algebraMap L (ResidueField L))).toCotangent ⟨_, hm⟩) = 0 := by
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
    have hmap := congrArg (KaehlerDifferential.map k k R L) (D_eq_add k hxy Dx Dy h1 h2 h3 h4 f)
    rw [map_add, map_smul, map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D,
      KaehlerDifferential.map_D, ← algebraMap_smul L (Dx f), ← algebraMap_smul L (Dy f)] at hmap
    rw [hmap, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      ← algebraMap_smul (ResidueField L),
      ← algebraMap_smul (ResidueField L) (algebraMap R L (Dy f)),
      hmax _ hfx, hmax _ hfy, zero_smul, zero_smul, add_zero]
  have h0 := hinj (key.trans (map_zero _).symm)
  have hker : RingHom.ker (algebraMap L (ResidueField L)) = maximalIdeal L := ker_residue
  rw [Ideal.toCotangent_eq_zero] at h0
  have h0' : algebraMap R L f ∈ RingHom.ker (algebraMap L (ResidueField L)) ^ 2 := h0
  rwa [hker] at h0'

omit [PerfectField k] [Algebra.EssFiniteType k R] [Module.Finite k (ResidueField R)] in
/-- In a two-dimensional local domain, a nonzero prime below a non-maximal prime equals it. -/
private theorem eq_of_le_of_ne_bot [IsNoetherianRing R] [IsDomain R] (hdim : ringKrullDim R = 2)
    {P Q : Ideal R} [P.IsPrime] [Q.IsPrime] (hP : P ≠ maximalIdeal R) (hQP : Q ≤ P)
    (hQ : Q ≠ ⊥) : Q = P := by
  by_contra hne
  have h0 : (⊥ : Ideal R).height < Q.height :=
    Ideal.height_strict_mono_of_isPrime (bot_lt_iff_ne_bot.2 hQ)
  have h1 : Q.height < P.height := Ideal.height_strict_mono_of_isPrime (hQP.lt_of_ne hne)
  have h2 : P.height < (maximalIdeal R).height := Ideal.height_strict_mono_of_isPrime
    (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hP)
  have h3 : (maximalIdeal R).height = 2 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hdim] at this
    exact WithBot.coe_inj.mp this
  rw [h3] at h2
  have key : ∀ a b c : ℕ∞, a < b → b < c → c < 2 → False := by
    intro a b c hab hbc hc
    lift c to ℕ using ne_top_of_lt hc
    lift b to ℕ using ne_top_of_lt hbc
    lift a to ℕ using ne_top_of_lt hab
    norm_cast at hab hbc hc
    omega
  exact key _ _ _ h0 h1 h2

omit [PerfectField k] [Algebra.EssFiniteType k R] [Module.Finite k (ResidueField R)] in
/-- At a non-maximal prime `P ∋ f` of a two-dimensional local domain with `R ⧸ (f)` reduced and
`f ≠ 0`, the maximal ideal of `R_P` is contained in the ideal generated by `f`. -/
private theorem maximalIdeal_le_span_singleton [IsNoetherianRing R] [IsDomain R]
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime] (hP : P ≠ maximalIdeal R) (f : R)
    (hf0 : f ≠ 0) (hfP : f ∈ P) (hred : IsReduced (R ⧸ Ideal.span {f})) :
    maximalIdeal (Localization.AtPrime P) ≤
      Ideal.span {algebraMap R (Localization.AtPrime P) f} := by
  set L := Localization.AtPrime P
  have hrad : (Ideal.span {f}).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2 hred
  have hmap : Ideal.span {algebraMap R L f} = (Ideal.span {f}).map (algebraMap R L) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hradL : (Ideal.span {algebraMap R L f}).IsRadical := by
    rintro a ⟨n, hn⟩
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
    rw [← IsLocalization.mk'_pow, hmap] at hn
    have hn' : algebraMap R L (r ^ n) ∈ (Ideal.span {f}).map (algebraMap R L) := by
      have := Ideal.mul_mem_right (algebraMap R L (s ^ n : P.primeCompl)) _ hn
      rwa [IsLocalization.mk'_spec] at this
    obtain ⟨t, ht, htr⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl L _ _).1 hn'
    have htr' : t * r ∈ Ideal.span {f} := hrad ⟨n, by
      rcases n with _ | n
      · simp only [pow_zero, mul_one] at htr
        exact absurd ((Ideal.span_singleton_le_iff_mem P).2 hfP htr) ht
      · rw [mul_pow, pow_succ t, mul_assoc]
        exact Ideal.mul_mem_left _ _ htr⟩
    rw [hmap]
    have hu : IsUnit (algebraMap R L t) := IsLocalization.map_units L (⟨t, ht⟩ : P.primeCompl)
    have := Ideal.mem_map_of_mem (algebraMap R L) htr'
    rw [map_mul] at this
    change IsLocalization.mk' L r s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ ((Ideal.unit_mul_mem_iff_mem _ hu).1 this)
  calc maximalIdeal L ≤ (Ideal.span {algebraMap R L f}).radical := by
        rw [Ideal.radical_eq_sInf]
        refine le_sInf fun Q' ⟨hle, hQ'⟩ => ?_
        have hQ'P : Q'.comap (algebraMap R L) ≤ P :=
          (Ideal.comap_mono (le_maximalIdeal hQ'.ne_top)).trans_eq
            (Localization.AtPrime.under_maximalIdeal (I := P))
        have hfQ : f ∈ Q'.comap (algebraMap R L) := hle (Ideal.mem_span_singleton_self _)
        have hne : Q'.comap (algebraMap R L) ≠ ⊥ := fun h => hf0 (Ideal.mem_bot.mp (h ▸ hfQ))
        have hQP := eq_of_le_of_ne_bot hdim hP hQ'P hne
        have hQP' : Ideal.under R Q' = P := hQP
        rw [← IsLocalization.map_under P.primeCompl L Q', hQP',
          Localization.AtPrime.map_eq_maximalIdeal]
    _ = _ := hradL.radical

/-- A nonzero element `g` of a local domain with `𝔪 ≤ (g)` does not lie in `𝔪²`. -/
private theorem notMem_maximalIdeal_sq_of_le_span_singleton {A : Type*} [CommRing A]
    [IsLocalRing A] [IsDomain A] {g : A} (hg0 : g ≠ 0) (hle : maximalIdeal A ≤ Ideal.span {g}) :
    g ∉ maximalIdeal A ^ 2 := by
  intro h
  have hg : g ∈ maximalIdeal A := Ideal.pow_le_self two_ne_zero h
  have h' := Ideal.pow_right_mono hle 2 h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h'
  obtain ⟨a, ha⟩ := h'
  have : g * (a * g - 1) = 0 := by
    rw [mul_sub, mul_one, mul_comm g, mul_assoc, ← sq, ha, sub_self]
  rcases mul_eq_zero.1 this with h0 | h1
  · exact hg0 h0
  · exact (mem_maximalIdeal _).1 hg
      (isUnit_iff_exists_inv.2 ⟨a, by linear_combination h1⟩)

/-- **Generic smoothness of a reduced curve germ.** Every prime containing the Jacobian ideal
`(f, Dx f, Dy f)` of a nonzero `f` with `R ⧸ (f)` reduced is the maximal ideal. -/
private theorem eq_maximalIdeal_of_jacobian_le {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) (Dx Dy : Derivation k R R)
    (h1 : Dx x = 1) (h2 : Dx y = 0) (h3 : Dy x = 0) (h4 : Dy y = 1)
    (f : R) (hf : f ≠ 0) (hred : IsReduced (R ⧸ Ideal.span {f}))
    (P : Ideal R) [P.IsPrime] (hJP : Ideal.span {f, Dx f, Dy f} ≤ P) : P = maximalIdeal R := by
  have : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing k R
  have : IsRegularLocalRing R := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hxy
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have hdim : ringKrullDim R = 2 := by rw [hxy.2]; rfl
  by_contra hP
  have hfP : f ∈ P := hJP (Ideal.subset_span (by simp))
  have hsq := algebraMap_mem_maximalIdeal_sq k hxy Dx Dy h1 h2 h3 h4 P f hfP
    (hJP (Ideal.subset_span (by simp))) (hJP (Ideal.subset_span (by simp)))
  have hle := maximalIdeal_le_span_singleton hdim P hP f hf hfP hred
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  exact notMem_maximalIdeal_sq_of_le_span_singleton
    (fun h => hf (hinj (h.trans (map_zero _).symm))) hle hsq

/-- The Jacobian quotient `R ⧸ (f, Dx f, Dy f)` of a reduced curve germ has finite length. -/
private theorem isFiniteLength_quotient_jacobian {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) (Dx Dy : Derivation k R R)
    (h1 : Dx x = 1) (h2 : Dx y = 0) (h3 : Dy x = 0) (h4 : Dy y = 1)
    (f : R) (hf : f ≠ 0) (hred : IsReduced (R ⧸ Ideal.span {f})) :
    IsFiniteLength R (R ⧸ Ideal.span {f, Dx f, Dy f}) := by
  have : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing k R
  set J := Ideal.span {f, Dx f, Dy f}
  have hdim0 : Ring.KrullDimLE 0 (R ⧸ J) := Ring.KrullDimLE.mk₀ fun I hI => by
    have hc : (I.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ _
    have hJc : J ≤ I.comap (Ideal.Quotient.mk J) := fun a ha => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact I.zero_mem
    have hm := eq_maximalIdeal_of_jacobian_le k hxy Dx Dy h1 h2 h3 h4 f hf hred _ hJc
    have hmax : (I.comap (algebraMap R (R ⧸ J))).IsMaximal := by
      rw [Ideal.Quotient.algebraMap_eq, hm]
      infer_instance
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under I hmax
  have : IsArtinianRing (R ⧸ J) := isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2
    ⟨inferInstance, hdim0⟩
  exact (isFiniteLength_iff_isNoetherian_isArtinian).2 ⟨inferInstance,
    isArtinian_of_surjective_algebraMap (R := R ⧸ J) Ideal.Quotient.mk_surjective⟩

omit [PerfectField k] [Algebra.EssFiniteType k R] [Module.Finite k (ResidueField R)] in
/-- If `R ⧸ J` has finite length then so does `R^ ⧸ J R^` (it is `R ⧸ J` again). -/
private theorem isFiniteLength_adicCompletion_quotient_map [IsNoetherianRing R] (J : Ideal R)
    (hJ : IsFiniteLength R (R ⧸ J)) :
    IsFiniteLength R^ (R^ ⧸ J.map (algebraMap R R^)) := by
  obtain ⟨hN, hA⟩ := (isFiniteLength_iff_isNoetherian_isArtinian).1 hJ
  have : IsArtinianRing (R ⧸ J) := isArtinian_of_tower R hA
  obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient J
  set K := J.map (algebraMap R R^)
  let φ : R →+* R^ ⧸ K := (Ideal.Quotient.mk K).comp (algebraMap R R^)
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨r, hr⟩ := Submodule.mkQ_surjective _ (AdicCompletion.eval (maximalIdeal R) R n z)
    refine ⟨r, Eq.symm (Ideal.Quotient.eq.2 ?_)⟩
    have hk : z - AdicCompletion.of (maximalIdeal R) R r ∈
        (AdicCompletion.eval (maximalIdeal R) R n).ker := by
      rw [LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, hr, sub_self]
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian _)] at hk
    refine Submodule.smul_induction_on hk (fun a ha b _ => ?_) (fun _ _ h1 h2 => K.add_mem h1 h2)
    rw [Algebra.smul_def]
    exact K.mul_mem_right _ (Ideal.mem_map_of_mem _ (hn ha))
  have hφ' : ∀ r, algebraMap R (R^ ⧸ K) r = φ r := fun r => by
    rw [IsScalarTower.algebraMap_apply R R^ (R^ ⧸ K), Ideal.Quotient.algebraMap_eq]
    rfl
  let ψ : (R ⧸ J) →ₗ[R] R^ ⧸ K := J.liftQ (Algebra.linearMap R (R^ ⧸ K)) fun a ha => by
    rw [LinearMap.mem_ker, Algebra.linearMap_apply, hφ']
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨r, rfl⟩ := hφ z
    exact ⟨Submodule.Quotient.mk r, by
      rw [Submodule.liftQ_apply, Algebra.linearMap_apply, hφ']⟩
  exact isFiniteLength_iff_isNoetherian_isArtinian.2
    ⟨isNoetherian_of_tower R (isNoetherian_of_surjective (f := ψ) (LinearMap.range_eq_top.2 hψ)),
      isArtinian_of_tower R (isArtinian_of_surjective _ ψ hψ)⟩

end Steps

/-- **The completed Jacobian quotient of a reduced curve germ has finite length.** Let `k` be a
perfect field and `R` a local `k`-algebra, essentially of finite type, with residue field finite
over `k` and regular system of parameters `x, y`. Then there are the coordinate `k`-derivations
`Dx, Dy` of `R` (`Dx x = 1`, `Dx y = 0`, `Dy x = 0`, `Dy y = 1`) and continuous `k`-derivations
`∂x, ∂y` of `R^ = AdicCompletion (maximalIdeal R) R` extending them, and for every nonzero
`f ∈ R` with `R ⧸ (f)` reduced, `R^ ⧸ (f, ∂x f, ∂y f)` is an `R^`-module of finite length. -/
@[mmp "lem_mmp_resolution_isolated_curve_jacobian_finite_length"]
public theorem exists_derivation_isFiniteLength_adicCompletion_quotient_jacobian
    (k : Type*) [Field k] [PerfectField k] {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra k R] [Algebra.EssFiniteType k R] [Module.Finite k (ResidueField R)]
    {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) :
    ∃ (Dx Dy : Derivation k R R)
      (δx δy : Derivation k (AdicCompletion (maximalIdeal R) R)
        (AdicCompletion (maximalIdeal R) R)),
      Dx x = 1 ∧ Dx y = 0 ∧ Dy x = 0 ∧ Dy y = 1 ∧
      (∀ r : R, δx (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
        algebraMap R (AdicCompletion (maximalIdeal R) R) (Dx r)) ∧
      (∀ r : R, δy (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
        algebraMap R (AdicCompletion (maximalIdeal R) R) (Dy r)) ∧
      @Continuous _ _
        ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))).adicTopology
        ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))).adicTopology δx ∧
      @Continuous _ _
        ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))).adicTopology
        ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))).adicTopology δy ∧
      ∀ f : R, f ≠ 0 → IsReduced (R ⧸ Ideal.span {f}) →
        IsFiniteLength (AdicCompletion (maximalIdeal R) R)
          (AdicCompletion (maximalIdeal R) R ⧸
            Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) f,
              δx (algebraMap R (AdicCompletion (maximalIdeal R) R) f),
              δy (algebraMap R (AdicCompletion (maximalIdeal R) R) f)}) := by
  have : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing k R
  obtain ⟨Dx, Dy, h1, h2, h3, h4⟩ := exists_coordinate_derivations k hxy
  set δx := extendDerivation (maximalIdeal R) Dx
  set δy := extendDerivation (maximalIdeal R) Dy
  have hδx := extendDerivation_algebraMap (maximalIdeal R) Dx
  have hδy := extendDerivation_algebraMap (maximalIdeal R) Dy
  refine ⟨Dx, Dy, δx, δy, h1, h2, h3, h4, hδx, hδy, continuous_derivation_adicTopology _ _,
    continuous_derivation_adicTopology _ _, fun f hf hred => ?_⟩
  have key := isFiniteLength_adicCompletion_quotient_map _
    (isFiniteLength_quotient_jacobian k hxy Dx Dy h1 h2 h3 h4 f hf hred)
  rw [hδx, hδy]
  rwa [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at key

/-- In a Noetherian local ring of Krull dimension at least `2`, the quotient by a principal ideal
contained in the maximal ideal does not have finite length. -/
private theorem not_isFiniteLength_quotient_span_singleton {A : Type*} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (hA : 2 ≤ ringKrullDim A) {w : A}
    (hw : w ∈ maximalIdeal A) : ¬ IsFiniteLength A (A ⧸ Ideal.span {w}) := by
  intro hfin
  have : IsArtinianRing (A ⧸ Ideal.span {w}) :=
    isArtinian_of_tower A (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  have h1 := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (Ideal.span {w})
    (by rwa [ringJacobson_eq_maximalIdeal, Ideal.span_singleton_le_iff_mem])
  have h2 : (Ideal.span {w}).spanFinrank ≤ 1 := by
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := A) (Set.finite_singleton w)
  have h3 : ringKrullDim (A ⧸ Ideal.span {w}) ≤ 0 := Ring.krullDimLE_iff.mp inferInstance
  have : ringKrullDim A ≤ 1 := h1.trans <| by simpa using add_le_add h3 (by exact_mod_cast h2)
  exact absurd (hA.trans this) (by norm_num)

/-- If `z ^ n` divides `a`, then `z ^ (n - 1)` divides every derivative of `a`. -/
private theorem pow_pred_dvd_derivation_of_pow_dvd {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (D : Derivation R A A) {z a : A} {n : ℕ} (h : z ^ n ∣ a) :
    z ^ (n - 1) ∣ D a := by
  obtain ⟨g, rfl⟩ := h
  rw [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    nsmul_eq_mul]
  exact dvd_add (dvd_mul_of_dvd_left (pow_dvd_pow z (n.sub_le 1)) _)
    (Dvd.dvd.mul_left (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _)

/-- **A reduced curve germ is not a formal `m`-th power.** Let `k` be a perfect field and `R` a
local `k`-algebra, essentially of finite type, with residue field finite over `k` and a regular
system of parameters `x, y`. If `f ∈ R` is nonzero with `R ⧸ (f)` reduced, then for every
`m ≥ 2` and every `z` in the extension of `maximalIdeal R` to `AdicCompletion (maximalIdeal R) R`,
the image of `f` in the completion is not in `Ideal.span {z ^ m}`. -/
@[mmp "lem_kr1c_reduced_curve_not_formal_mth_power"]
public theorem algebraMap_notMem_span_pow_adicCompletion
    (k : Type*) [Field k] [PerfectField k] {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra k R] [Algebra.EssFiniteType k R] [Module.Finite k (ResidueField R)]
    {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    {f : R} (hf : f ≠ 0) (hred : IsReduced (R ⧸ Ideal.span {f}))
    {m : ℕ} (hm : 2 ≤ m) {z : AdicCompletion (maximalIdeal R) R}
    (hz : z ∈ (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))) :
    algebraMap R (AdicCompletion (maximalIdeal R) R) f ∉ Ideal.span {z ^ m} := by
  rw [Ideal.mem_span_singleton]
  intro hdvd
  have : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing k R
  obtain ⟨_, hmax, -, -, -, -, -, hreg⟩ := MMP.Resolution.adicCompletion_maximalIdeal_package R
  obtain ⟨-, -, δx, δy, -, -, -, -, -, -, -, -, hfin⟩ :=
    exists_derivation_isFiniteLength_adicCompletion_quotient_jacobian k hxy
  have hle : Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) f,
      δx (algebraMap R (AdicCompletion (maximalIdeal R) R) f),
      δy (algebraMap R (AdicCompletion (maximalIdeal R) R) f)} ≤ Ideal.span {z ^ (m - 1)} := by
    simp only [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Ideal.mem_span_singleton]
    exact ⟨(pow_dvd_pow z (m.sub_le 1)).trans hdvd, pow_pred_dvd_derivation_of_pow_dvd δx hdvd,
      pow_pred_dvd_derivation_of_pow_dvd δy hdvd⟩
  exact not_isFiniteLength_quotient_span_singleton (by exact_mod_cast (hreg ![x, y] hxy).2.2.ge)
    (hmax ▸ Ideal.pow_mem_of_mem _ hz _ (by omega))
    ((hfin f hf hred).of_surjective (Submodule.factor_surjective hle))

end MMP.Resolution

end
