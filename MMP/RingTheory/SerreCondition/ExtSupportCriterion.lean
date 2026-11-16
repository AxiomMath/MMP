module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector

/-!
# An `Ext`-support criterion for `S₂`, and crepant junctions

This file holds two independent results.

**An `Ext`-support criterion.** Let `P = L[x₁, …, xₙ]` be a polynomial ring over a field `L`,
let `A = P ⧸ I` be a nonzero quotient, and let `c ≤ n` with `dim A ≤ n - c`. Then `A` is
equidimensional of dimension `n - c` and satisfies Serre's condition `S₂` if and only if, for
every `i > c`, the support of the `P`-module `Ext^i_P(A, P)` has codimension at least `i + 2` in
`Spec P`. The codimension of a set of primes is the infimum of their heights, so the empty set
has codimension `⊤`. The proof reads the criterion off the Auslander–Buchsbaum formula over the
regular local rings `P_𝔮`: the lowest degree in which `Ext^•_P(A, P)` is supported at `𝔮` is
`ht 𝔮 - depth A_𝔮`, and the dimension formula `dim A_𝔮 = ht 𝔮 - c` for equidimensional `A`.

**Crepant junctions.** For a crepant junction `(p, Θ)`, `p : Y ⟶ X`, of an effective rational
klt threefold pair `(X, B)` extracting a finite set `I` of valuations, `K_Y + Θ` is `ℚ`-Cartier
and `K_Y + Θ = p^*(K_X + B)`. Consequently the log discrepancies of `(Y, Θ)` and `(X, B)` agree
at every divisorial valuation of the common function field `k(Y) ≅ k(X)`.

## Main results

* `MMP.Algebra.equidimensional_and_s2_iff_ext_support`: the `Ext`-support criterion.
* `MMP.Fourfold.CrepantJunction.isCrepant`: `(Y, Θ)` is a pair, `Θ` is the crepant boundary of
  `(X, B)` on `Y` for every canonical divisor of `X`, and `a(ξ; Y, Θ) = a(ξ; X, B)` for every
  valuation `ξ` of `k(Y)`.

## Implementation notes

* Equidimensionality of dimension `n - c` is stated as `dim (A ⧸ 𝔭) = n - c` for every minimal
  prime `𝔭` of `A`. Condition `S₂` is `min 2 (dim A_𝔮) ≤ depth A_𝔮` for every prime `𝔮` of `A`,
  with depth `ringDepth`. The `Ext` groups are those of `ModuleCat P`, with the
  `P`-module structure coming from the `P`-linearity of that category.
* "`K_Y + Θ` is `ℚ`-Cartier" is `MMP.Fourfold.IsPair (p ≫ s_X) Θ`; "`K_Y + Θ = p^*(K_X + B)`" is
  `MMP.Mori.IsCrepantBoundary`: `-coeff_F Θ` is the discrepancy `a(F, X, B)` of every prime
  divisor `F` of `Y`, computed from any canonical divisor `K` of `X`. At a non-exceptional `F`
  this holds because `p` is an isomorphism over the generic point of the centre of `F`; at an
  exceptional `E_s` it is the choice `coeff_{E_s} Θ = 1 - a(s; X, B)`.
* The log discrepancy of a valuation is `MMP.Fourfold.IsValuationLogDiscrepancy`, a predicate on
  the value, false for a valuation that is not divisorial. A valuation `ξ` of `k(Y)` is compared
  with `ξ ∘ p^*` on `k(X)`; since `p` is birational every valuation of `k(X)` arises so, a
  divisor over `X` being realized over `Y` by the valuative criterion for `p`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98], 2.25, 2.30.
-/

universe u v

namespace MMP.Algebra

open CategoryTheory Abelian

section ExtLocalization

variable {R : Type v} [CommRing R] (S : Submonoid R)

private theorem subsingleton_iff_surjective_of_exact {T : Type*} [Ring T] {A B C : Type*}
    [AddCommGroup A] [Module T A] [AddCommGroup B] [Module T B] [AddCommGroup C] [Module T C]
    {φ : A →ₗ[T] B} {χ : B →ₗ[T] C} (h : Function.Exact φ χ) (hχ : Function.Surjective χ) :
    Subsingleton C ↔ Function.Surjective φ := by
  refine ⟨fun _ b => (h b).1 (Subsingleton.elim _ _),
    fun hφ => subsingleton_of_forall_eq 0 fun z => ?_⟩
  obtain ⟨b, rfl⟩ := hχ z
  obtain ⟨a, rfl⟩ := hφ b
  exact h.apply_apply_eq_zero a

/-- Surjectivity is transported along equivalences intertwining two maps. -/
private theorem surjective_iff_of_equiv_comm {A B C D : Type*} {φ : A → C} {ψ : B → D}
    (eA : A ≃ B) (eC : C ≃ D) (h : ∀ x, eC (φ x) = ψ (eA x)) :
    Function.Surjective ψ ↔ Function.Surjective φ := by
  constructor
  · intro hψ z
    obtain ⟨w, hw⟩ := hψ (eC z)
    refine ⟨eA.symm w, eC.injective ?_⟩
    rw [h, Equiv.apply_symm_apply, hw]
  · intro hφ y
    obtain ⟨x, hx⟩ := hφ (eC.symm y)
    exact ⟨eA x, by rw [← h, hx, Equiv.apply_symm_apply]⟩

private theorem subsingleton_localizedModule_congr {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) :
    Subsingleton (LocalizedModule S A) ↔ Subsingleton (LocalizedModule S B) :=
  (IsLocalizedModule.iso S
    ((LocalizedModule.mkLinearMap S B) ∘ₗ e.toLinearMap)).toEquiv.subsingleton_congr

/-- Over a projective middle term, precomposition with the extension class of a short exact
sequence is a bijection in positive degrees. -/
private theorem precomp_extClass_bijective {T : Type v} [CommRing T]
    {X : ShortComplex (ModuleCat.{v} T)} (hX : X.ShortExact) [Projective X.X₂]
    (N : ModuleCat.{v} T) (k : ℕ) :
    Function.Bijective (hX.extClass.precompOfLinear T N (add_comm 1 (k + 1))) := by
  refine ⟨?_, precomp_extClass_surjective_of_projective_X₂ N hX (k + 1)⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₁ hX N x (add_comm 1 (k + 1)) hx
  rw [Ext.eq_zero_of_projective y, Ext.comp_zero]

/-- The exact sequence `Ext⁰(X₂, N) → Ext⁰(X₁, N) → Ext¹(X₃, N) → 0` of a short exact sequence
with projective middle term. -/
private theorem exact_extZero_extOne {T : Type v} [CommRing T]
    {X : ShortComplex (ModuleCat.{v} T)} (hX : X.ShortExact) [Projective X.X₂]
    (N : ModuleCat.{v} T) :
    Function.Exact ((Ext.mk₀ X.f).precompOfLinear T N (zero_add 0))
      (hX.extClass.precompOfLinear T N (add_comm 1 0)) ∧
    Function.Surjective (hX.extClass.precompOfLinear T N (add_comm 1 0)) := by
  refine ⟨fun y => ⟨fun hy => ?_, ?_⟩, precomp_extClass_surjective_of_projective_X₂ N hX 0⟩
  · exact Ext.contravariant_sequence_exact₁ hX N y (add_comm 1 0) hy
  · rintro ⟨x, rfl⟩
    change hX.extClass.comp ((Ext.mk₀ X.f).comp x (zero_add 0)) (add_comm 1 0) = 0
    rw [← Ext.comp_assoc_of_second_deg_zero, hX.extClass_comp, Ext.zero_comp]

private theorem linearEquiv₀_mk₀ {T : Type*} [Ring T] {C : Type*} [Category C] [Abelian C]
    [Linear T C] [HasExt C] {X Y : C} (a : X ⟶ Y) :
    Ext.linearEquiv₀ (R := T) (Ext.mk₀ a) = a := by
  rw [← Ext.linearEquiv₀_symm_apply (R := T)]
  exact LinearEquiv.apply_symm_apply _ _

variable {N : Type v} [AddCommGroup N] [Module R N]
  {N' : Type v} [AddCommGroup N'] [Module (Localization S) N'] [Module R N']
  [IsScalarTower R (Localization S) N'] (g : N →ₗ[R] N') [IsLocalizedModule S g]

/-- The localization map on `Ext⁰`, with values in linear maps between localizations. -/
private noncomputable def extZeroLocalization {M M' : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module (Localization S) M'] [Module R M']
    [IsScalarTower R (Localization S) M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] :
    Ext (ModuleCat.of R M) (ModuleCat.of R N) 0 →ₗ[R] (M' →ₗ[Localization S] N') :=
  IsLocalizedModule.mapExtendScalars S f g (Localization S) ∘ₗ
    (Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv).toLinearMap

private theorem isLocalizedModule_extZeroLocalization [IsNoetherianRing R] {M M' : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M'] [Module (Localization S) M'] [Module R M']
    [IsScalarTower R (Localization S) M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] :
    IsLocalizedModule S (extZeroLocalization S g f) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact IsLocalizedModule.of_linearEquiv_right _ _ _

private theorem extZeroLocalization_comp {K K' F F' : Type v} [AddCommGroup K] [Module R K]
    [AddCommGroup K'] [Module (Localization S) K'] [Module R K']
    [IsScalarTower R (Localization S) K'] (fK : K →ₗ[R] K') [IsLocalizedModule S fK]
    [AddCommGroup F] [Module R F]
    [AddCommGroup F'] [Module (Localization S) F'] [Module R F']
    [IsScalarTower R (Localization S) F'] (fF : F →ₗ[R] F') [IsLocalizedModule S fF]
    (ι : K →ₗ[R] F) (x : Ext (ModuleCat.of R F) (ModuleCat.of R N) 0) :
    extZeroLocalization S g fK ((Ext.mk₀ (ModuleCat.ofHom ι)).comp x (zero_add 0)) =
      extZeroLocalization S g fF x ∘ₗ
        IsLocalizedModule.mapExtendScalars S fK fF (Localization S) ι := by
  obtain ⟨h, rfl⟩ := Ext.homEquiv₀.symm.surjective x
  rw [Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀]
  ext a
  simp only [extZeroLocalization, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.trans_apply, linearEquiv₀_mk₀, IsLocalizedModule.mapExtendScalars_apply_apply]
  rw [show ModuleCat.homLinearEquiv (ModuleCat.ofHom ι ≫ h) = h.hom ∘ₗ ι from rfl,
    IsLocalizedModule.map_comp' S fK fF g]
  rfl

/-- The `Rₛ`-linear equivalence `Ext⁰(X, Y) ≃ (X →ₗ Y)` over a ring. -/
private noncomputable abbrev extZeroEquiv {T : Type v} [CommRing T] (X Y : Type v)
    [AddCommGroup X] [Module T X] [AddCommGroup Y] [Module T Y] :
    Ext (ModuleCat.of T X) (ModuleCat.of T Y) 0 ≃ₗ[T] (X →ₗ[T] Y) :=
  Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv

private theorem extZeroEquiv_comp {T : Type v} [CommRing T] {X Y Z : Type v}
    [AddCommGroup X] [Module T X] [AddCommGroup Y] [Module T Y] [AddCommGroup Z] [Module T Z]
    (ι : X →ₗ[T] Y) (x : Ext (ModuleCat.of T Y) (ModuleCat.of T Z) 0) :
    extZeroEquiv X Z ((Ext.mk₀ (ModuleCat.ofHom ι)).comp x (zero_add 0)) =
      extZeroEquiv Y Z x ∘ₗ ι := by
  obtain ⟨h, rfl⟩ := Ext.homEquiv₀.symm.surjective x
  rw [Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀]
  simp only [extZeroEquiv, LinearEquiv.trans_apply, linearEquiv₀_mk₀]
  rfl

/-- Localizing the presentation `ker π ↪ F ↠ M` at `S` gives a short exact sequence. -/
private theorem shortExact_localizedModule_presentation {M F : Type v} [AddCommGroup M]
    [Module R M] [AddCommGroup F] [Module R F] {M' : Type v} [AddCommGroup M']
    [Module (Localization S) M'] [Module R M'] [IsScalarTower R (Localization S) M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (π : F →ₗ[R] M) (hπ : Function.Surjective π) :
    ∃ w, (ShortComplex.mk (ModuleCat.ofHom (IsLocalizedModule.mapExtendScalars S
        (LocalizedModule.mkLinearMap S (LinearMap.ker π)) (LocalizedModule.mkLinearMap S F)
          (Localization S) (LinearMap.ker π).subtype))
      (ModuleCat.ofHom (IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S F) f
        (Localization S) π)) w).ShortExact := by
  let K := LinearMap.ker π
  let ι' : LocalizedModule S K →ₗ[Localization S] LocalizedModule S F :=
    IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S K)
      (LocalizedModule.mkLinearMap S F) (Localization S) K.subtype
  let π' : LocalizedModule S F →ₗ[Localization S] M' :=
    IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S F) f (Localization S) π
  have hex : Function.Exact ι' π' :=
    IsLocalizedModule.map_exact S _ _ _ K.subtype π (LinearMap.exact_subtype_ker_map π)
  have hinj : Function.Injective ι' :=
    IsLocalizedModule.map_injective S _ _ K.subtype Subtype.val_injective
  have hsurj : Function.Surjective π' := IsLocalizedModule.map_surjective S _ _ π hπ
  exact ⟨by ext x; exact hex.apply_apply_eq_zero x, ShortComplex.ShortExact.mk'
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hex)
    ((ModuleCat.mono_iff_injective _).2 hinj) ((ModuleCat.epi_iff_surjective _).2 hsurj)⟩

include g in
/-- `Ext` of finite modules over a Noetherian ring commutes with localization, in the weak form
that the localization of `Extⁿ_R(M, N)` vanishes exactly when `Extⁿ` of the localized modules
vanishes. -/
private theorem subsingleton_localizedModule_ext_iff [IsNoetherianRing R] (n : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
      (M' : Type v) [AddCommGroup M'] [Module (Localization S) M'] [Module R M']
      [IsScalarTower R (Localization S) M'] (f : M →ₗ[R] M') [IsLocalizedModule S f],
      Subsingleton (LocalizedModule S (Ext (ModuleCat.of R M) (ModuleCat.of R N) n)) ↔
        Subsingleton
          (Ext (ModuleCat.of (Localization S) M') (ModuleCat.of (Localization S) N') n) := by
  induction n with
  | zero =>
    intro M _ _ _ M' _ _ _ _ f _
    have := isLocalizedModule_extZeroLocalization S g f
    rw [(IsLocalizedModule.iso S (extZeroLocalization S g f)).toEquiv.subsingleton_congr]
    exact (extZeroEquiv (T := Localization S) M' N').toEquiv.subsingleton_congr.symm
  | succ n ih =>
    intro M _ _ _ M' _ _ _ _ f _
    obtain ⟨F, _, _, _, _, π, hπ⟩ := Module.exists_finite_presentation R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have : Projective (ModuleCat.of R F) := (IsProjective.iff_projective F).1 inferInstance
    obtain ⟨hw, hX'⟩ := shortExact_localizedModule_presentation S f π hπ
    let X' : ShortComplex (ModuleCat.{v} (Localization S)) := ShortComplex.mk _ _ hw
    replace hX' : X'.ShortExact := hX'
    have : Projective X'.X₂ :=
      (IsProjective.iff_projective (LocalizedModule S F)).1 inferInstance
    rcases n with _ | k
    · obtain ⟨hexR, hsurjR⟩ := exact_extZero_extOne hS (ModuleCat.of R N)
      obtain ⟨hexS, hsurjS⟩ := exact_extZero_extOne hX' (ModuleCat.of (Localization S) N')
      let lF := extZeroLocalization S g (LocalizedModule.mkLinearMap S F)
      let lK := extZeroLocalization S g (LocalizedModule.mkLinearMap S K)
      have : IsLocalizedModule S lF :=
        isLocalizedModule_extZeroLocalization S g (LocalizedModule.mkLinearMap S F)
      have : IsLocalizedModule S lK :=
        isLocalizedModule_extZeroLocalization S g (LocalizedModule.mkLinearMap S K)
      let ψ : (LocalizedModule S F →ₗ[Localization S] N') →ₗ[R]
          (LocalizedModule S K →ₗ[Localization S] N') :=
        (LinearMap.lcomp (Localization S) N' X'.f.hom).restrictScalars R
      have hmap : IsLocalizedModule.map S lF lK
          ((Ext.mk₀ π.shortComplexKer.f).precompOfLinear R (ModuleCat.of R N) (zero_add 0)) =
            ψ := by
        symm
        apply IsLocalizedModule.ext S lF (IsLocalizedModule.map_units lK)
        rw [IsLocalizedModule.map_comp]
        ext x : 1
        exact (extZeroLocalization_comp S g _ _ K.subtype x).symm
      rw [subsingleton_iff_surjective_of_exact
        (IsLocalizedModule.map_exact S lF lK (LocalizedModule.mkLinearMap S _) _ _ hexR)
        (IsLocalizedModule.map_surjective S lK (LocalizedModule.mkLinearMap S _) _ hsurjR),
        hmap, subsingleton_iff_surjective_of_exact hexS hsurjS]
      exact surjective_iff_of_equiv_comm
        (extZeroEquiv (T := Localization S) (LocalizedModule S F) N').toEquiv
        (extZeroEquiv (T := Localization S) (LocalizedModule S K) N').toEquiv
        fun x => extZeroEquiv_comp X'.f.hom x
    · rw [subsingleton_localizedModule_congr S
        (LinearEquiv.ofBijective _ (precomp_extClass_bijective hS (ModuleCat.of R N) k)).symm,
        ← (Equiv.ofBijective _ (precomp_extClass_bijective hX'
          (ModuleCat.of (Localization S) N') k)).subsingleton_congr]
      exact ih K (LocalizedModule S K) (LocalizedModule.mkLinearMap S K)

end ExtLocalization

/-- The support of `Ext^i_R(M, N)` is detected after localizing at the prime. -/
private theorem ext_localization_support_iff {R : Type v} [CommRing R] [IsNoetherianRing R]
    (M N : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (i : ℕ) (q : PrimeSpectrum R) :
    q ∈ Module.support R (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R N) i) ↔
      Nontrivial (Abelian.Ext
        (ModuleCat.of (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M))
        (ModuleCat.of (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl N)) i) := by
  rw [Module.mem_support_iff, ← not_subsingleton_iff_nontrivial, ← not_subsingleton_iff_nontrivial,
    subsingleton_localizedModule_ext_iff q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N) i M _
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)]

section ExtTopDegree

variable {R : Type v} [CommRing R]

/-- If `Ext^{n+2}(M, -)` vanishes and `g : X → Y` is surjective, then `Ext^{n+1}(M, X) = 0`
implies `Ext^{n+1}(M, Y) = 0`. -/
private theorem ext_subsingleton_of_surjective (M : ModuleCat.{v} R) (n : ℕ)
    [HasProjectiveDimensionLT M (n + 2)] {X Y : Type v} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (g : X →ₗ[R] Y) (hg : Function.Surjective g)
    [Subsingleton (Ext M (ModuleCat.of R X) (n + 1))] :
    Subsingleton (Ext M (ModuleCat.of R Y) (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ M (LinearMap.shortExact_shortComplexKer hg) y
    (n₁ := n + 2) rfl (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 2) le_rfl)
  rw [← hx, Subsingleton.elim x 0, Ext.zero_comp]

/-- Generators of `L` other than the first generate the quotient of `L` by the first. -/
private theorem span_range_mkQ_succ {L : Type*} [AddCommGroup L] [Module R L] {m : ℕ}
    (s : Fin (m + 1) → L) (hs : Submodule.span R (Set.range s) = ⊤) :
    Submodule.span R (Set.range (fun i : Fin m => (Submodule.span R {s 0}).mkQ (s i.succ))) =
      ⊤ := by
  set N := Submodule.span R {s 0}
  have hr : Set.range s = insert (s 0) (Set.range (fun i : Fin m => s i.succ)) := by
    rw [← Fin.range_cons (s 0) (fun i : Fin m => s i.succ)]
    exact congrArg Set.range (Fin.cons_self_tail s).symm
  rw [hr, Submodule.span_insert] at hs
  have : Set.range (fun i : Fin m => N.mkQ (s i.succ)) =
      N.mkQ '' Set.range (fun i : Fin m => s i.succ) := by
    rw [← Set.range_comp]; rfl
  rw [this, ← Submodule.map_span, eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := N.mkQ_surjective x
  have hy : y ∈ N ⊔ Submodule.span R (Set.range (fun i : Fin m => s i.succ)) := by
    rw [hs]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  refine ⟨b, hb, ?_⟩
  simp [(Submodule.Quotient.mk_eq_zero N).2 ha]

/-- If `M` has projective dimension at most `n + 1` and `Ext^{n+1}(M, R) = 0`, then
`Ext^{n+1}(M, L) = 0` for every finitely generated `L`. -/
private theorem ext_subsingleton_of_fg (M : ModuleCat.{v} R) (n : ℕ)
    [HasProjectiveDimensionLT M (n + 2)]
    (h : Subsingleton (Ext M (ModuleCat.of R R) (n + 1))) :
    ∀ (m : ℕ) (L : Type v) [AddCommGroup L] [Module R L] (s : Fin m → L),
      Submodule.span R (Set.range s) = ⊤ → Subsingleton (Ext M (ModuleCat.of R L) (n + 1)) := by
  intro m
  induction m with
  | zero =>
    intro L _ _ s hs
    have : Subsingleton L := by
      rw [← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top, ← hs]
      simp
    exact ext_subsingleton_of_surjective M n (0 : R →ₗ[R] L)
      (fun y => ⟨0, Subsingleton.elim _ _⟩)
  | succ m ih =>
    intro L _ _ s hs
    let N : Submodule R L := Submodule.span R {s 0}
    have hS := LinearMap.shortExact_shortComplexKer (Submodule.mkQ_surjective N)
    have h₃ : Subsingleton (Ext M (ModuleCat.of R (L ⧸ N)) (n + 1)) :=
      ih (L ⧸ N) (fun i => N.mkQ (s i.succ)) (span_range_mkQ_succ s hs)
    have h₁ : Subsingleton (Ext M (ModuleCat.of R (LinearMap.ker N.mkQ)) (n + 1)) := by
      refine ext_subsingleton_of_surjective M n
        (LinearMap.toSpanSingleton R _ ⟨s 0, by simp [N, Submodule.mem_span_singleton_self]⟩) ?_
      rintro ⟨z, hz⟩
      rw [Submodule.ker_mkQ, Submodule.mem_span_singleton] at hz
      obtain ⟨r, rfl⟩ := hz
      exact ⟨r, rfl⟩
    refine subsingleton_of_forall_eq 0 fun y => ?_
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ M hS y (Subsingleton.elim _ _)
    rw [← hx, Subsingleton.elim x 0, Ext.zero_comp]

/-- A nonzero finite module `M` of finite projective dimension `p` over a Noetherian ring has
`Ext^p(M, R) ≠ 0`. -/
private theorem nontrivial_ext_projectiveDimension [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] (p : ℕ) (hp : projectiveDimension (ModuleCat.of R M) = p) :
    Nontrivial (Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R R) p) := by
  cases p with
  | zero =>
    have hproj : Module.Projective R M :=
      (IsProjective.iff_projective M).2 ((projectiveDimension_eq_zero_iff _).1 hp).1
    obtain ⟨s, hs⟩ := Module.projective_def'.1 hproj
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    have hsx : s x ≠ 0 := fun h0 => hx (by simpa [h0] using (LinearMap.congr_fun hs x).symm)
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hsx
    let φ : M →ₗ[R] R := Finsupp.lapply i ∘ₗ s
    have : Nontrivial (ModuleCat.of R M ⟶ ModuleCat.of R R) := by
      refine ⟨⟨ModuleCat.ofHom φ, 0, fun h => hi ?_⟩⟩
      simpa [φ] using congrArg (fun f => f.hom x) h
    exact Ext.homEquiv₀.nontrivial
  | succ k =>
    by_contra hne
    rw [not_nontrivial_iff_subsingleton] at hne
    have : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 2) := by
      rw [← projectiveDimension_lt_iff, hp]
      exact_mod_cast Nat.lt_succ_self _
    have hlt := ModuleCat.hasProjectiveDimensionLT_of_forall_finite (ModuleCat.of R M) (k + 1)
      (fun L _ => by
        obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := L)
        exact ext_subsingleton_of_fg (ModuleCat.of R M) k hne m L s hs)
    rw [← projectiveDimension_lt_iff, hp] at hlt
    exact lt_irrefl _ hlt

end ExtTopDegree

section PolynomialQuotient

variable {L : Type v} [Field L] {n : ℕ}

local notation "P" => MvPolynomial (Fin n) L

/-- The height of the preimage in `P` of a prime of `P ⧸ I`, as a natural number. -/
private noncomputable abbrev ht {I : Ideal P} (𝔮 : PrimeSpectrum (P ⧸ I)) : ℕ :=
  (𝔮.asIdeal.comap (Ideal.Quotient.mk I)).height.toNat

/-- The depth of the localization of `P ⧸ I` at a prime, as a natural number. -/
private noncomputable abbrev dp {I : Ideal P} (𝔮 : PrimeSpectrum (P ⧸ I)) : ℕ :=
  (ringDepth (Localization.AtPrime 𝔮.asIdeal)).toNat

/-- Heights of primes of `P` are finite and at most `n`. -/
private theorem height_comap_eq {I : Ideal P} (𝔮 : PrimeSpectrum (P ⧸ I)) :
    (𝔮.asIdeal.comap (Ideal.Quotient.mk I)).height = (ht 𝔮 : ℕ∞) ∧ ht 𝔮 ≤ n := by
  have h1 : ((𝔮.asIdeal.comap (Ideal.Quotient.mk I)).height : WithBot ℕ∞) ≤ (n : ℕ∞) := by
    have := Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔮.asIdeal.comap (Ideal.Quotient.mk I))
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at this
    simpa using this
  have h2 : (𝔮.asIdeal.comap (Ideal.Quotient.mk I)).height ≤ n := by exact_mod_cast h1
  have h3 : (𝔮.asIdeal.comap (Ideal.Quotient.mk I)).height ≠ ⊤ := ne_top_of_le_ne_top (by simp) h2
  refine ⟨(ENat.natCast_toNat h3).symm, ?_⟩
  exact_mod_cast (ENat.natCast_toNat h3).symm ▸ h2

/-- The depth of the local ring at `𝔮` is the finite value `dp 𝔮`. -/
private theorem depth_eq_dp {I : Ideal P} (𝔮 : PrimeSpectrum (P ⧸ I)) :
    ringDepth (Localization.AtPrime 𝔮.asIdeal) = (dp 𝔮 : ℕ∞) := by
  refine (ENat.natCast_toNat fun h => ?_).symm
  have := Module.depth_le_ringKrullDim (Localization.AtPrime 𝔮.asIdeal)
  rw [← ringDepth_eq_depth_maximalIdeal, h] at this
  exact ringKrullDim_ne_top (top_le_iff.mp this)

/-- Dimension formula for a prime `𝔮` of the polynomial ring: `ht 𝔮 + dim P/𝔮 = n`. -/
private theorem height_add_coheight_eq (𝔮 : PrimeSpectrum P) :
    𝔮.asIdeal.height + Order.coheight 𝔮 = n := by
  have hP : ringKrullDim P = n := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]; simp
  have h1 := MMP.ringKrullDim_le_height_add_coheight L P 𝔮
  have h2 := Order.height_add_coheight_le_krullDim 𝔮
  rw [← WithBot.coe_add] at h2
  rw [PrimeSpectrum.height_eq_orderHeight]
  change _ ≤ ringKrullDim _ at h2
  rw [hP] at h1 h2
  exact_mod_cast le_antisymm h2 h1

/-- `(R ⧸ I) ⧸ 𝔮` and `R ⧸ 𝔮.comap (mk I)` have the same dimension. -/
private theorem ringKrullDim_quotient_quotient {R : Type*} [CommRing R] (I : Ideal R)
    (𝔮 : Ideal (R ⧸ I)) :
    ringKrullDim ((R ⧸ I) ⧸ 𝔮) = ringKrullDim (R ⧸ 𝔮.comap (Ideal.Quotient.mk I)) := by
  refine ringKrullDim_eq_of_ringEquiv ?_
  have hs : Function.Surjective ((Ideal.Quotient.mk 𝔮).comp (Ideal.Quotient.mk I)) :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  refine (RingHom.quotientKerEquivOfSurjective hs).symm.trans (Ideal.quotEquivOfEq ?_)
  rw [← RingHom.comap_ker, Ideal.mk_ker]

/-- The dimension of `R ⧸ 𝔮` is the coheight of `𝔮` in `Spec R`. -/
private theorem ringKrullDim_quotient_eq_coheight {R : Type*} [CommRing R] (Q : PrimeSpectrum R) :
    ringKrullDim (R ⧸ Q.asIdeal) = Order.coheight Q := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  congr 2

/-- Dimension formula for a prime of `P ⧸ I`: `dim (P ⧸ I) ⧸ 𝔮 = n - ht 𝔮`. -/
private theorem ringKrullDim_quotient_eq {I : Ideal P} (𝔮 : PrimeSpectrum (P ⧸ I)) :
    ringKrullDim ((P ⧸ I) ⧸ 𝔮.asIdeal) = ((n - ht 𝔮 : ℕ) : WithBot ℕ∞) := by
  set Q := PrimeSpectrum.comap (Ideal.Quotient.mk I) 𝔮
  rw [ringKrullDim_quotient_quotient]
  change ringKrullDim (P ⧸ Q.asIdeal) = _
  rw [ringKrullDim_quotient_eq_coheight]
  have h := height_add_coheight_eq Q
  obtain ⟨hh, hn⟩ := height_comap_eq 𝔮
  change Q.asIdeal.height = _ at hh
  rw [hh] at h
  have hc : Order.coheight Q = ((n - ht 𝔮 : ℕ) : ℕ∞) := by
    have hne : Order.coheight Q ≠ ⊤ := fun ht => by simp [ht] at h
    rw [← ENat.natCast_toNat hne] at h ⊢
    norm_cast at h ⊢
    omega
  rw [hc]
  rfl

/-- Along a strict chain the height grows at least by the length of the chain. -/
private theorem height_head_add_length_le {α : Type*} [Preorder α] (t : LTSeries α) :
    Order.height t.head + t.length ≤ Order.height t.last := by
  have key : ∀ m : ℕ, (m : ℕ∞) ≤ Order.height t.head →
      ((m + t.length : ℕ) : ℕ∞) ≤ Order.height t.last := by
    intro m hm
    obtain ⟨u, hu, hl⟩ := Order.exists_series_of_le_height _ hm
    simpa [hl] using Order.length_le_height_last (p := u.smash t hu)
  cases h : Order.height t.head with
  | top =>
    rw [top_add, top_le_iff, ENat.eq_top_iff_forall_ge]
    intro m
    exact le_trans (by exact_mod_cast Nat.le_add_right m _) (key m (by simp [h]))
  | coe a => exact_mod_cast key a h.ge

/-- For primes `𝔭 ≤ 𝔮` of `P ⧸ I`, the height of `𝔮` in `Spec (P ⧸ I)` is at least
`ht 𝔮 - ht 𝔭`. -/
private theorem sub_le_height_of_le {I : Ideal P} {𝔭 𝔮 : PrimeSpectrum (P ⧸ I)}
    (hpq : 𝔭.asIdeal ≤ 𝔮.asIdeal) : ((ht 𝔮 - ht 𝔭 : ℕ) : ℕ∞) ≤ Order.height 𝔮 := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk 𝔭.asIdeal) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk 𝔭.asIdeal) ≤ 𝔮.asIdeal := by
    rwa [Ideal.mk_ker]
  let qb : PrimeSpectrum ((P ⧸ I) ⧸ 𝔭.asIdeal) :=
    ⟨𝔮.asIdeal.map (Ideal.Quotient.mk 𝔭.asIdeal), Ideal.map_isPrime_of_surjective hsurj hker⟩
  have hqb : PrimeSpectrum.comap (Ideal.Quotient.mk 𝔭.asIdeal) qb = 𝔮 := by
    ext1
    exact (Ideal.comap_map_of_surjective' _ hsurj _).trans (sup_eq_left.mpr hker)
  have hco : Order.coheight qb = ((n - ht 𝔮 : ℕ) : ℕ∞) := by
    have h := ringKrullDim_quotient_eq_coheight qb
    rw [ringKrullDim_quotient_quotient] at h
    have h' : qb.asIdeal.comap (Ideal.Quotient.mk 𝔭.asIdeal) = 𝔮.asIdeal :=
      congrArg (·.asIdeal) hqb
    rw [h', ringKrullDim_quotient_eq 𝔮] at h
    exact WithBot.coe_injective h.symm
  have h1 := MMP.ringKrullDim_le_height_add_coheight L ((P ⧸ I) ⧸ 𝔭.asIdeal) qb
  rw [ringKrullDim_quotient_eq 𝔭, hco] at h1
  have h1' : ((n - ht 𝔭 : ℕ) : ℕ∞) ≤ Order.height qb + ((n - ht 𝔮 : ℕ) : ℕ∞) :=
    WithBot.coe_le_coe.mp h1
  have h2 : Order.height qb ≤ Order.height 𝔮 := hqb ▸
    Order.height_le_height_apply_of_strictMono _ (RingHom.strictMono_comap_of_surjective hsurj) qb
  have hq := (height_comap_eq 𝔮).2
  refine le_trans ?_ h2
  cases h : Order.height qb with
  | top => simp
  | coe a =>
    rw [h] at h1'
    norm_cast at h1' ⊢
    omega

/-- If every minimal prime of `A = P ⧸ I` has height `c`, then `dim A_𝔮 = ht 𝔮 - c`. -/
private theorem ringKrullDim_localization_eq {I : Ideal P} {c : ℕ}
    (hmin : ∀ 𝔭 ∈ minimalPrimes (P ⧸ I),
      (𝔭.comap (Ideal.Quotient.mk I)).height = (c : ℕ∞))
    (𝔮 : PrimeSpectrum (P ⧸ I)) :
    ringKrullDim (Localization.AtPrime 𝔮.asIdeal) = ((ht 𝔮 - c : ℕ) : WithBot ℕ∞) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮.asIdeal, PrimeSpectrum.height_eq_orderHeight]
  suffices h : Order.height 𝔮 = ((ht 𝔮 - c : ℕ) : ℕ∞) by rw [h]; rfl
  have hmono : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  have hht : ∀ 𝔯 : PrimeSpectrum (P ⧸ I),
      Order.height (PrimeSpectrum.comap (Ideal.Quotient.mk I) 𝔯) = (ht 𝔯 : ℕ∞) := fun 𝔯 => by
    rw [← PrimeSpectrum.height_eq_orderHeight]; exact (height_comap_eq 𝔯).1
  have hc : ∀ 𝔯 : PrimeSpectrum (P ⧸ I), 𝔯.asIdeal ∈ minimalPrimes (P ⧸ I) → ht 𝔯 = c :=
    fun 𝔯 h𝔯 => by
      have := (height_comap_eq 𝔯).1
      rw [hmin _ h𝔯] at this
      exact_mod_cast this.symm
  have hle : ∀ 𝔯 𝔰 : PrimeSpectrum (P ⧸ I), 𝔯 ≤ 𝔰 → ht 𝔯 ≤ ht 𝔰 := fun 𝔯 𝔰 h => by
    have := Order.height_mono (hmono.monotone h)
    rw [hht, hht] at this
    exact_mod_cast this
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ 𝔮.asIdeal)
  let 𝔭 : PrimeSpectrum (P ⧸ I) := ⟨p, hp.1.1⟩
  apply le_antisymm
  · refine Order.height_le fun t htl => ?_
    obtain ⟨p', hp', hp't⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ t.head.asIdeal)
    have h1 := height_head_add_length_le (t.map _ hmono)
    have h2 := hle ⟨p', hp'.1.1⟩ t.head hp't
    rw [hc _ hp'] at h2
    rw [LTSeries.head_map, LTSeries.last_map, LTSeries.map_length, htl, hht, hht] at h1
    have : ht t.head + t.length ≤ ht 𝔮 := by exact_mod_cast h1
    exact_mod_cast (by omega : t.length ≤ ht 𝔮 - c)
  · rw [← hc 𝔭 hp]
    exact sub_le_height_of_le hpq

/-- At a minimal prime the localization is Artinian, so has depth zero. -/
private theorem dp_eq_zero_of_mem_minimalPrimes {I : Ideal P} (𝔭 : PrimeSpectrum (P ⧸ I))
    (h𝔭 : 𝔭.asIdeal ∈ minimalPrimes (P ⧸ I)) : dp 𝔭 = 0 := by
  have : Ring.KrullDimLE 0 (Localization.AtPrime 𝔭.asIdeal) :=
    Ring.KrullDimLE.of_isLocalization 𝔭.asIdeal h𝔭 _
  suffices h : ringDepth (Localization.AtPrime 𝔭.asIdeal) = 0 by simp [dp, h]
  refine le_antisymm (iSup₂_le fun rs hrs => ?_) bot_le
  cases rs with
  | nil => simp
  | cons r rs =>
    exfalso
    obtain ⟨k, hk⟩ :=
      Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr (hrs.1 r List.mem_cons_self)
    have h1 := ((RingTheory.Sequence.isRegular_cons_iff _ r rs).mp hrs.2).1.pow k
    rw [hk] at h1
    exact IsSMulRegular.not_zero_iff.mpr inferInstance h1

/-- The map `P_𝔮 → A_𝔮` induced by the quotient map is surjective. -/
private theorem localRingHom_quotientMk_surjective {I : Ideal P} (𝔮 : PrimeSpectrum (P ⧸ I)) :
    Function.Surjective (Localization.localRingHom (𝔮.asIdeal.comap (Ideal.Quotient.mk I))
      𝔮.asIdeal (Ideal.Quotient.mk I) rfl) := by
  intro x
  obtain ⟨⟨a, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.asIdeal.primeCompl x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  refine ⟨IsLocalization.mk' _ a
    (⟨s, hs⟩ : (𝔮.asIdeal.comap (Ideal.Quotient.mk I)).primeCompl), ?_⟩
  rw [Localization.localRingHom_mk']

/-- **Auslander–Buchsbaum for a cyclic module over a regular local ring.** Let `R` be a regular
local ring of dimension `h` and `B` a nonzero quotient ring of `R`, of depth `d` as an `R`-module.
Then `d ≤ h`, `Ext^{h - d}_R(B, R) ≠ 0`, and `Ext^i_R(B, R) ≠ 0` forces `i + d ≤ h`. -/
private theorem ext_of_isRegularLocalRing {R B : Type v} [CommRing R] [IsRegularLocalRing R]
    [CommRing B] [Nontrivial B] [Algebra R B] (hf : Function.Surjective (algebraMap R B))
    {h d : ℕ} (hR : ringKrullDim R = ((h : ℕ∞) : WithBot ℕ∞))
    (hd : Module.depth R (IsLocalRing.maximalIdeal R) B = d) :
    d ≤ h ∧ Nontrivial (Ext (ModuleCat.of R B) (ModuleCat.of R R) (h - d)) ∧
      ∀ i : ℕ, Nontrivial (Ext (ModuleCat.of R B) (ModuleCat.of R R) i) → i + d ≤ h := by
  have : IsNoetherianRing R := IsRegularLocalRing.toIsNoetherian
  have hdepthR : Module.depth R (IsLocalRing.maximalIdeal R) R = (h : ℕ∞) := by
    have := depth_eq_ringKrullDim_of_isRegularLocalRing R
    rw [hR] at this
    exact_mod_cast this
  have : Module.Finite R B := Module.Finite.of_surjective (Algebra.linearMap R B) hf
  have hle : HasProjectiveDimensionLE (ModuleCat.of R B) h :=
    (Stacks.RegularLocalRing.ShortFreeResolution.solution hR.le).2 _
  have hpdle : projectiveDimension (ModuleCat.of R B) ≤ (h : WithBot ℕ∞) :=
    (projectiveDimension_le_iff _ _).2 hle
  have hpdbot : projectiveDimension (ModuleCat.of R B) ≠ ⊥ := by
    rw [Ne, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    exact not_subsingleton B
  have htop : (h : WithBot ℕ∞) ≠ ⊤ := by
    rw [← WithBot.coe_natCast, ← WithBot.coe_top, Ne, WithBot.coe_inj]
    exact ENat.natCast_ne_top h
  have hAB := Module.projectiveDimension_add_depth_eq_depth_self (R := R) B
    (ne_top_of_le_ne_top htop hpdle)
  rw [hd, hdepthR] at hAB
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hpdbot
  change projectiveDimension (ModuleCat.of R B) + _ = _ at hAB
  rw [← he] at hAB
  have he' : e + (d : ℕ∞) = (h : ℕ∞) := by exact_mod_cast hAB
  have hetop : e ≠ ⊤ := fun h => by simp [h] at he'
  obtain ⟨p, rfl⟩ := ENat.ne_top_iff_exists.mp hetop
  have hp : p + d = h := by exact_mod_cast he'
  have hpd : projectiveDimension (ModuleCat.of R B) = (p : WithBot ℕ∞) := he.symm
  refine ⟨by omega, ?_, fun i hi => ?_⟩
  · rw [show h - d = p by omega]
    exact nontrivial_ext_projectiveDimension B p hpd
  · by_contra hlt
    have : HasProjectiveDimensionLT (ModuleCat.of R B) (p + 1) := by
      rw [← projectiveDimension_lt_iff, hpd]
      exact_mod_cast Nat.lt_succ_self p
    obtain ⟨x, y, hxy⟩ := hi.exists_pair_ne
    exact hxy ((Ext.eq_zero_of_hasProjectiveDimensionLT x (p + 1) (by omega)).trans
      (Ext.eq_zero_of_hasProjectiveDimensionLT y (p + 1) (by omega)).symm)

open MvPolynomial in
/-- **Auslander–Buchsbaum over `P_𝔮`.** At a prime `𝔮` of `A = P ⧸ I`, with `h = ht 𝔮` and
`d = depth A_𝔮`: `d ≤ h`, `Ext^{h - d}_P(A, P)` is supported at `𝔮`, and `Ext^i_P(A, P)` is
supported at `𝔮` only if `i + d ≤ h`. -/
private theorem ext_support_at {I : Ideal P} (𝔮 : PrimeSpectrum (P ⧸ I)) :
    dp 𝔮 ≤ ht 𝔮 ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk I) 𝔮 ∈ Module.support P
        (Ext (ModuleCat.of P (P ⧸ I)) (ModuleCat.of P P) (ht 𝔮 - dp 𝔮)) ∧
      ∀ i : ℕ, PrimeSpectrum.comap (Ideal.Quotient.mk I) 𝔮 ∈ Module.support P
        (Ext (ModuleCat.of P (P ⧸ I)) (ModuleCat.of P P) i) → i + dp 𝔮 ≤ ht 𝔮 := by
  set Q := 𝔮.asIdeal.comap (Ideal.Quotient.mk I) with hQ
  let R := Localization.AtPrime Q
  let B := Localization.AtPrime 𝔮.asIdeal
  let f : R →+* B := Localization.localRingHom Q 𝔮.asIdeal (Ideal.Quotient.mk I) rfl
  have hf : Function.Surjective f := localRingHom_quotientMk_surjective 𝔮
  let : Algebra R B := f.toAlgebra
  have : IsRegularRing P :=
    (isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization.{v, 0, v}
      L (Fin n)).1
  have : IsRegularLocalRing R := IsRegularRing.isRegularLocalRing_localization Q
  have hdimR : ringKrullDim R = ((ht 𝔮 : ℕ∞) : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q R, (height_comap_eq 𝔮).1]
  have hdB : Module.depth R (IsLocalRing.maximalIdeal R) B = (dp 𝔮 : ℕ∞) := by
    rw [Stacks.CohenMacaulay.BaseFieldExtension.depth_eq_depth_map hf _ (AddEquiv.refl B)
      (fun a x => rfl), IsLocalRing.map_maximalIdeal_of_surjective f hf,
      ← ringDepth_eq_depth_maximalIdeal]
    exact depth_eq_dp 𝔮
  obtain ⟨h1, h2, h3⟩ := ext_of_isRegularLocalRing (R := R) (B := B) hf hdimR hdB
  -- `Ext` of `A` into `P` localizes to `Ext` of `A_𝔮` into `P_𝔮`
  let : IsScalarTower P R B := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap P B x = f (algebraMap P R x)
    rw [IsScalarTower.algebraMap_apply P (P ⧸ I) B]
    exact (Localization.localRingHom_to_map Q 𝔮.asIdeal (Ideal.Quotient.mk I) rfl x).symm
  have hsub : Algebra.algebraMapSubmonoid (P ⧸ I) Q.primeCompl = 𝔮.asIdeal.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨?_, fun hx => ⟨y, hx, rfl⟩⟩
    rintro ⟨z, hz, hzy⟩ hmem
    have hzz : Ideal.Quotient.mk I z = Ideal.Quotient.mk I y := hzy
    exact hz (show Ideal.Quotient.mk I z ∈ 𝔮.asIdeal by rwa [hzz])
  have : IsLocalizedModule Q.primeCompl (IsScalarTower.toAlgHom P (P ⧸ I) B).toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, hsub]
    infer_instance
  have hext : ∀ i : ℕ, PrimeSpectrum.comap (Ideal.Quotient.mk I) 𝔮 ∈ Module.support P
      (Ext (ModuleCat.of P (P ⧸ I)) (ModuleCat.of P P) i) ↔
        Nontrivial (Ext (ModuleCat.of R B) (ModuleCat.of R R) i) := fun i => by
    rw [Module.mem_support_iff, ← not_subsingleton_iff_nontrivial,
      ← not_subsingleton_iff_nontrivial]
    exact not_congr (subsingleton_localizedModule_ext_iff (N := P) (N' := R) Q.primeCompl
      (Algebra.linearMap P R) i (P ⧸ I) B (IsScalarTower.toAlgHom P (P ⧸ I) B).toLinearMap)
  exact ⟨h1, (hext _).2 h2, fun i hi => h3 i ((hext i).1 hi)⟩

/-- Auslander–Buchsbaum, vanishing half: at a prime in the support of `Ext^i_P(A, P)`,
`depth + i ≤ height`. -/
private theorem exists_of_mem_support_ext {I : Ideal P} {i : ℕ} {𝔮 : PrimeSpectrum P}
    (h : 𝔮 ∈ Module.support P (Ext (ModuleCat.of P (P ⧸ I)) (ModuleCat.of P P) i)) :
    ∃ 𝔮' : PrimeSpectrum (P ⧸ I), PrimeSpectrum.comap (Ideal.Quotient.mk I) 𝔮' = 𝔮 ∧
      dp 𝔮' + i ≤ ht 𝔮' := by
  by_cases hI : I ≤ 𝔮.asIdeal
  · have hmem : 𝔮 ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
      rwa [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    obtain ⟨𝔮', rfl⟩ := hmem
    exact ⟨𝔮', rfl, by have := (ext_support_at 𝔮').2.2 i h; omega⟩
  · exfalso
    have hA : 𝔮 ∉ Module.support P (P ⧸ I) := by
      rwa [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    rw [Module.notMem_support_iff] at hA
    rw [ext_localization_support_iff] at h
    have : HasProjectiveDimensionLT (ModuleCat.of (Localization.AtPrime 𝔮.asIdeal)
        (LocalizedModule 𝔮.asIdeal.primeCompl (P ⧸ I))) 0 :=
      (ModuleCat.isZero_of_subsingleton _).hasProjectiveDimensionLT_zero
    obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
    exact hxy ((Ext.eq_zero_of_hasProjectiveDimensionLT x 0 (by omega)).trans
      (Ext.eq_zero_of_hasProjectiveDimensionLT y 0 (by omega)).symm)

private theorem min_two_le_iff (a b : ℕ) :
    min 2 ((a : ℕ) : WithBot ℕ∞) ≤ (((b : ℕ) : ℕ∞) : WithBot ℕ∞) ↔ min 2 a ≤ b := by
  have : min (2 : WithBot ℕ∞) ((a : ℕ) : WithBot ℕ∞) = (((min 2 a : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rcases le_total 2 a with h | h
    · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]; rfl
    · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]; rfl
  rw [this]
  exact_mod_cast Iff.rfl

/-- The `Ext`-support bound, read at a prime `𝔮` of `A` in the lowest degree `ht 𝔮 - dp 𝔮` where
`Ext^•_P(A, P)` is supported at `𝔮`: if that degree exceeds `c`, it is at most `ht 𝔮 - 2`. -/
private theorem sub_add_two_le_of_lt {I : Ideal P} {c : ℕ}
    (hext : ∀ i : ℕ, c < i → ((i + 2 : ℕ) : ℕ∞) ≤ ⨅ 𝔮 ∈ Module.support P
      (Ext (ModuleCat.of P (P ⧸ I)) (ModuleCat.of P P) i), 𝔮.asIdeal.height)
    (𝔮 : PrimeSpectrum (P ⧸ I)) (hj : c < ht 𝔮 - dp 𝔮) : ht 𝔮 - dp 𝔮 + 2 ≤ ht 𝔮 := by
  have := (hext _ hj).trans (iInf₂_le _ (ext_support_at 𝔮).2.1)
  change _ ≤ (𝔮.asIdeal.comap (Ideal.Quotient.mk I)).height at this
  rwa [(height_comap_eq 𝔮).1, Nat.cast_le] at this

end PolynomialQuotient

/-- **`Ext`-support criterion for `S₂`.** For a nonzero quotient `A = P ⧸ I` of
`P = L[x₁, …, xₙ]` with `dim A ≤ n - c`, `A` is equidimensional of dimension `n - c` and
satisfies `S₂` iff `codim_P Supp Ext^i_P(A, P) ≥ i + 2` for all `i > c`. -/
@[mmp "lem_mmp_ext_support_s2_criterion"]
public theorem equidimensional_and_s2_iff_ext_support {L : Type u} [Field L] {n c : ℕ}
    (I : Ideal (MvPolynomial (Fin n) L)) (_hI : I ≠ ⊤) (hc : c ≤ n)
    (hdim : ringKrullDim (MvPolynomial (Fin n) L ⧸ I) ≤ ((n - c : ℕ) : WithBot ℕ∞)) :
    ((∀ 𝔭 ∈ minimalPrimes (MvPolynomial (Fin n) L ⧸ I),
        ringKrullDim ((MvPolynomial (Fin n) L ⧸ I) ⧸ 𝔭) = ((n - c : ℕ) : WithBot ℕ∞)) ∧
      ∀ 𝔮 : PrimeSpectrum (MvPolynomial (Fin n) L ⧸ I),
        min 2 (ringKrullDim (Localization.AtPrime 𝔮.asIdeal)) ≤
          ((ringDepth (Localization.AtPrime 𝔮.asIdeal) : ℕ∞) : WithBot ℕ∞)) ↔
      ∀ i : ℕ, c < i →
        ((i + 2 : ℕ) : ℕ∞) ≤ ⨅ 𝔮 ∈ Module.support (MvPolynomial (Fin n) L)
          (Ext (ModuleCat.of (MvPolynomial (Fin n) L) (MvPolynomial (Fin n) L ⧸ I))
            (ModuleCat.of (MvPolynomial (Fin n) L) (MvPolynomial (Fin n) L)) i),
          𝔮.asIdeal.height := by
  -- minimal primes have height `c` iff `dim A/𝔭 = n - c`
  have hmin_iff : ∀ 𝔭 : PrimeSpectrum (MvPolynomial (Fin n) L ⧸ I),
      ringKrullDim ((MvPolynomial (Fin n) L ⧸ I) ⧸ 𝔭.asIdeal) = ((n - c : ℕ) : WithBot ℕ∞) ↔
        ht 𝔭 = c := by
    intro 𝔭
    rw [ringKrullDim_quotient_eq]
    have := (height_comap_eq 𝔭).2
    rw [Nat.cast_inj]
    omega
  constructor
  · rintro ⟨heq, hs2⟩ i hi
    refine le_iInf₂ fun 𝔮 h𝔮 => ?_
    obtain ⟨𝔮', rfl, hle⟩ := exists_of_mem_support_ext h𝔮
    have hmin : ∀ 𝔭 ∈ minimalPrimes (MvPolynomial (Fin n) L ⧸ I),
        (𝔭.comap (Ideal.Quotient.mk I)).height = (c : ℕ∞) := fun 𝔭 h𝔭 => by
      have := (hmin_iff ⟨𝔭, h𝔭.1.1⟩).1 (heq 𝔭 h𝔭)
      rw [(height_comap_eq ⟨𝔭, h𝔭.1.1⟩).1, this]
    have h2 := hs2 𝔮'
    rw [ringKrullDim_localization_eq hmin, depth_eq_dp, min_two_le_iff] at h2
    change ((i + 2 : ℕ) : ℕ∞) ≤ (𝔮'.asIdeal.comap (Ideal.Quotient.mk I)).height
    rw [(height_comap_eq 𝔮').1, Nat.cast_le]
    omega
  · intro hext
    have hminc : ∀ 𝔭 : PrimeSpectrum (MvPolynomial (Fin n) L ⧸ I),
        𝔭.asIdeal ∈ minimalPrimes (MvPolynomial (Fin n) L ⧸ I) → ht 𝔭 = c := by
      intro 𝔭 h𝔭
      have hd := dp_eq_zero_of_mem_minimalPrimes 𝔭 h𝔭
      have hle : ringKrullDim ((MvPolynomial (Fin n) L ⧸ I) ⧸ 𝔭.asIdeal) ≤
          ((n - c : ℕ) : WithBot ℕ∞) := (ringKrullDim_quotient_le _).trans hdim
      rw [ringKrullDim_quotient_eq, Nat.cast_le] at hle
      have hn := (height_comap_eq 𝔭).2
      by_contra hne
      have := sub_add_two_le_of_lt hext 𝔭 (by omega)
      omega
    have hmin : ∀ 𝔭 ∈ minimalPrimes (MvPolynomial (Fin n) L ⧸ I),
        (𝔭.comap (Ideal.Quotient.mk I)).height = (c : ℕ∞) := fun 𝔭 h𝔭 => by
      rw [(height_comap_eq ⟨𝔭, h𝔭.1.1⟩).1, hminc ⟨𝔭, h𝔭.1.1⟩ h𝔭]
    refine ⟨fun 𝔭 h𝔭 => (hmin_iff ⟨𝔭, h𝔭.1.1⟩).2 (hminc ⟨𝔭, h𝔭.1.1⟩ h𝔭), fun 𝔮 => ?_⟩
    rw [ringKrullDim_localization_eq hmin, depth_eq_dp, min_two_le_iff]
    have hdh := (ext_support_at 𝔮).1
    by_cases hj : c < ht 𝔮 - dp 𝔮
    · have := sub_add_two_le_of_lt hext 𝔮 hj
      omega
    · omega

end MMP.Algebra

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry MMP.Mori

section CanonicalDivisorExistence

open Opposite TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

omit [IsLocallyNoetherian X] [IsNormal X] [IsDominant U.ι] in
private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

omit [IsLocallyNoetherian X] [IsNormal X] [IsDominant U.ι] in
private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The unique irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, TopCat.Presheaf.stalkSpecializes_comp_apply,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨x, hx, hxe⟩
      rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      rw [← hx]
      exact x.2
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · intro h E' hE'
    exact (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

omit [IsLocallyNoetherian X] [IsNormal X] in
private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · have h' : restrictRF U V ψ₁.1 = restrictRF U V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective U V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictOpen_iso (D : Divisor X) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] :
    Nonempty (Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm⟩

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  have : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS with hT
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  have : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  have : IsDominant T.ι := Opens.isDominant_ι (T.isOpen.dense ⟨_, (Classical.arbitrary T).2⟩)
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  have : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  have : IsIntegral T := inferInstance
  have : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso KS T
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

section ValuationLift

/-- A valuation `ξ'` of `ℂ(X')` restricting on `ℂ(Z)` to the valuation of a divisor `D` over a
model `X ⟶ Z` is a divisor of the function field `ℂ(X')`: it is `ord_E` on the normal variety
`D.Y`, transported along `ℂ(X') ≅ ℂ(Z) ≅ ℂ(D.Y)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g')
    (D : DivisorOver ℂ (g ≫ sZ)) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    MMP.Flips.IsDivisorOfFunctionField ℂ (g' ≫ sZ) ξ' := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have hY : IsNormalVariety ℂ ((D.f ≫ g) ≫ sZ) := by
    rw [Category.assoc]; exact D.isNormalVariety
  have hbij : Function.Bijective (functionFieldMap (D.f ≫ g)) := by
    have : ⇑(functionFieldMap (D.f ≫ g)) = functionFieldMap D.f ∘ functionFieldMap g := by
      funext t
      exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g t).symm
    rw [this]
    exact D.isBirationalMorphism.functionFieldMap_bijective.comp hg.functionFieldMap_bijective
  refine ⟨D.Y, (D.f ≫ g) ≫ sZ, hY, D.E, ?_⟩
  let := MMP.Mori.functionFieldAlgebra sZ
  let := MMP.Mori.functionFieldAlgebra (g' ≫ sZ)
  let := MMP.Mori.functionFieldAlgebra ((D.f ≫ g) ≫ sZ)
  let eP := MMP.Mori.functionFieldAlgEquiv sZ g' hg'.functionFieldMap_bijective
  let eY := MMP.Mori.functionFieldAlgEquiv sZ (D.f ≫ g) hbij
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hg'.functionFieldMap_bijective.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  have h1 : eP.symm (functionFieldMap g' s) = s := eP.symm_apply_apply s
  change ξ' (functionFieldMap g' s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap g' s)))
  rw [h1, hs]
  change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g s)) = _
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g s]
  rfl

/-- **The centre on a proper model.** Let `g : X ⟶ Z` and `g' : X' ⟶ Z` be dominant morphisms of
integral schemes with `g'` proper, and `D` a divisor over `X`. A valuation `ξ'` of `k(X')`
restricting on `k(Z)` to `ord_D` dominates the local ring of some point of `X'`: the valuation
ring of `ξ'` dominates `𝒪_{Z, g(c_X(D))}`, and the valuative criterion for `g'` lifts
`Spec 𝒪_{ξ'} ⟶ Z` to `X'`. -/
private theorem exists_dominated_point_of_comap_eq {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
    (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g'] (hgp' : IsProper g')
    (D : DivisorOver k sX) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ x : X', (∀ a : X'.presheaf.stalk x, ξ' (algebraMap _ X'.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X'.presheaf.stalk x),
        ξ' (algebraMap _ X'.functionField a) < 1 := by
  set y := D.f D.E.genericPoint
  set z := g y
  have hw : ∀ b : Z.presheaf.stalk z,
      ξ' (functionFieldMap g' (algebraMap _ Z.functionField b)) =
        D.valuation (algebraMap _ X.functionField ((g.stalkMap y).hom b)) := by
    intro b
    have := congrArg (fun v => v (algebraMap _ Z.functionField b)) h
    simp only [Valuation.comap_apply] at this
    rw [this, functionFieldMap_algebraMap_stalk g y b]
  let R := ξ'.valuationSubring
  let φ : Z.presheaf.stalk z →+* R :=
    ((functionFieldMap g').comp (algebraMap (Z.presheaf.stalk z) Z.functionField)).codRestrict R
      fun b => (ξ'.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl _)
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hex : ValuativeCriterion.Existence g' := by
    have h : @IsProper _ _ g' := hgp'
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq g' :=
    { R := R
      K := X'.functionField
      i₁ := X'.fromSpecStalk (genericPoint X')
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk g',
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R X'.functionField)) ≫ l =
      X'.fromSpecStalk (genericPoint X') := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint X' ⤳ x := (genericPoint_spec X').specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R X'.functionField) =
      X'.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (X'.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : X'.presheaf.stalk x,
      algebraMap _ X'.functionField a = ((f.hom a : R) : X'.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]; exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

/-- Over a proper birational model `X' ⟶ Z` of a normal variety, a valuation `ξ'` of `ℂ(X')`
restricting on `ℂ(Z)` to the valuation of a divisor over another model `X ⟶ Z` is realized by a
proper divisor over `X'`. -/
private theorem exists_properDivisorOver_valuation_eq_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX' : IsNormalVariety ℂ sX') (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hgp' : IsProper g')
    (hc : g ≫ sZ = sX) (hc' : g' ≫ sZ = sX') (D : DivisorOver ℂ sX)
    (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ D' : DivisorOver ℂ sX', IsProper D'.f ∧ D'.valuation = ξ' := by
  obtain ⟨x, h1, h2⟩ := exists_dominated_point_of_comap_eq g g' hgp' D ξ' h
  have : AlgebraicGeometry.IsVariety ℂ sX' := hX'.1
  have hξ : MMP.Flips.IsDivisorOfFunctionField ℂ sX' ξ' := by
    subst hc hc'
    exact isDivisorOfFunctionField_of_comap_eq g g' hg hg' D ξ' h
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX' hξ x h1 h2
  exact ⟨D'.toDivisorOver, D'.isProper, hv⟩

end ValuationLift

section InverseTransform

variable {X Y : Scheme.{u}} {R : Type*} [AddCommMonoid R] {g : Y ⟶ X}

/-- The coefficient of `g⁻¹_*(D)` in `g⁻¹_* B` is that of `D` in `B`: the inverse transform of
prime divisors is injective, as `g` sends the generic point of `g⁻¹_*(D)` to that of `D`. -/
private theorem coeff_inverseTransformDivisor_of_eq_some {D : MMP.Mori.PrimeDivisor X}
    {F : MMP.Mori.PrimeDivisor Y} (hD : inverseTransformPrimeDivisor g D = some F)
    (B : DivisorWithCoeffs R X) : (inverseTransformDivisor g B).coeff F = B.coeff D :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hD (fun _ hD' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hD').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1) B

/-- A prime divisor of `Y` which is the inverse transform of no prime divisor of `X` has
coefficient zero in every inverse transform `g⁻¹_* B`. -/
private theorem coeff_inverseTransformDivisor_eq_zero {F : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P, inverseTransformPrimeDivisor g P ≠ some F) (B : DivisorWithCoeffs R X) :
    (inverseTransformDivisor g B).coeff F = 0 := by
  classical
  induction B using Finsupp.induction_linear with
  | zero => simp [DivisorWithCoeffs.coeff]
  | add B B' hB hB' =>
    rw [map_add, DivisorWithCoeffs.coeff, Finsupp.add_apply, ← DivisorWithCoeffs.coeff,
      ← DivisorWithCoeffs.coeff, hB, hB', add_zero]
  | single P r =>
    rw [inverseTransformDivisor_single]
    rcases hP : inverseTransformPrimeDivisor g P with _ | E
    · rfl
    · exact Finsupp.single_eq_of_ne fun hEF => h P (hEF ▸ hP)

end InverseTransform

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
  {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- The log discrepancy of a valuation is unique. -/
private theorem IsValuationLogDiscrepancy.unique
    {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a a' : ℝ} (h : IsValuationLogDiscrepancy sX B ξ a)
    (h' : IsValuationLogDiscrepancy sX B ξ a') : a = a' := by
  obtain ⟨n, D, -, hv, h⟩ := h
  obtain ⟨n', D', -, hv', h'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h h' (hv.trans hv'.symm)

omit [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- The inverse transform of an effective divisor is effective. -/
private theorem inverseTransformDivisor_nonneg {Y : Scheme.{0}} (g : Y ⟶ X) {D : QDivisor X}
    (hD : 0 ≤ D) : 0 ≤ inverseTransformDivisor g D := by
  classical
  rw [inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply,
    Finsupp.sum]
  refine Finset.sum_nonneg fun P _ => ?_
  cases inverseTransformPrimeDivisor g P with
  | none => exact le_rfl
  | some E => exact Finsupp.single_nonneg.mpr (hD P)

/-- A natural number equal to the dimension `3` of a space is `3`. -/
private theorem eq_three_of_topologicalKrullDim_eq {S : Type*} [TopologicalSpace S] {n : ℕ}
    (h : topologicalKrullDim S = n) (h3 : topologicalKrullDim S = 3) : n = 3 := by
  rw [h3] at h
  exact_mod_cast h.symm

private theorem isProper_p (J : CrepantJunction sX B I) : IsProper J.p :=
  isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism

/-- The boundary `Θ` of a crepant junction is effective. -/
private theorem Θ_nonneg (J : CrepantJunction sX B I) : 0 ≤ J.Θ := by
  obtain ⟨a, ha, hΘ⟩ := J.Θ_eq
  rw [hΘ]
  refine add_nonneg (inverseTransformDivisor_nonneg _ J.isKltPair.1.nonneg)
    (Finset.sum_nonneg fun s _ => Finsupp.single_nonneg.mpr ?_)
  obtain ⟨-, a', ha', ha'1⟩ := J.subset_lowDiscrepancySet s.2
  have : (a s : ℝ) ≤ 1 := IsValuationLogDiscrepancy.unique (ha s) ha' ▸ ha'1
  exact sub_nonneg.mpr (by exact_mod_cast this)

/-- The source of a junction has a canonical divisor. -/
private theorem exists_isCanonicalDivisor_Y (J : CrepantJunction sX B I) :
    ∃ K : Divisor J.Y, K.IsCanonicalDivisor (J.p ≫ sX) 3 := by
  have : QuasiCompact (J.p ≫ sX) := J.isQFactorial.1.1.toQuasiCompact
  have : CompactSpace J.Y := QuasiCompact.compactSpace_of_compactSpace (J.p ≫ sX)
  exact exists_isCanonicalDivisor (J.p ≫ sX) J.isQFactorial.1 (by rw [J.dim_eq]; rfl)

/-- `(Y, Θ)` is a pair: `Y` is `ℚ`-factorial, so `K_Y + Θ` is `ℚ`-Cartier, and `Θ ≥ 0`. -/
private theorem isPair (J : CrepantJunction sX B I) : MMP.Fourfold.IsPair (J.p ≫ sX) J.Θ := by
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor_Y J
  exact ⟨J.isKltPair.1.isAlgClosed, J.isKltPair.1.charZero, ⟨J.isQFactorial.1, 3, K, hK,
    MMP.Fourfold.isQCartier_of_isQFactorial _ J.isQFactorial _⟩, Θ_nonneg J⟩

/-- The divisor `(Y, p, F)` over `X` of a prime divisor `F` of the source of a junction. -/
private abbrev divisorOver (J : CrepantJunction sX B I) (F : MMP.Mori.PrimeDivisor J.Y) :
    DivisorOver ℂ sX :=
  ⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, F⟩

/-- No prime divisor of `X` has an exceptional prime divisor as its inverse transform: the generic
point of `E_s` maps to a point of codimension `≥ 2`, while that of a prime divisor has
codimension `1`. -/
private theorem inverseTransformPrimeDivisor_ne_E (J : CrepantJunction sX B I) (s : I)
    (P : MMP.Mori.PrimeDivisor X) : inverseTransformPrimeDivisor J.p P ≠ some (J.E s) := by
  intro hP
  have hX : IsSeparated (X ↘ ⊤_ Scheme) := by
    have := J.isKltPair.1.isPair.1.1
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  have hη := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hP).1
  have hexc := (J.isExceptional_iff (J.E s)).mpr ⟨s, rfl⟩
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight] at hexc
  have h2 := hexc (J.p (J.E s).genericPoint)
    (subset_closure ⟨_, (by
      change _ ∈ (J.E s).support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl), rfl⟩)
  rw [hη, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The coefficient of `Θ = p⁻¹_* B + ∑ (1 - a_s) E_s` along a prime divisor `F` of `Y`. -/
private theorem coeff_Θ (J : CrepantJunction sX B I) {a : I → ℚ}
    (hΘ : J.Θ = inverseTransformDivisor J.p B + ∑ s : I, Finsupp.single (J.E s) (1 - a s))
    (F : MMP.Mori.PrimeDivisor J.Y) :
    J.Θ.coeff F = (inverseTransformDivisor J.p B).coeff F +
      ∑ s : I, (Finsupp.single (J.E s) (1 - a s) : QDivisor J.Y) F := by
  rw [hΘ, DivisorWithCoeffs.coeff, Finsupp.add_apply, Finsupp.finsetSum_apply]
  rfl

/-- The coefficient of `Θ` along `E_s` is `1 - a(s; X, B)`. -/
private theorem coeff_Θ_E (J : CrepantJunction sX B I) {a : I → ℚ}
    (hΘ : J.Θ = inverseTransformDivisor J.p B + ∑ s : I, Finsupp.single (J.E s) (1 - a s))
    (s : I) : J.Θ.coeff (J.E s) = 1 - a s := by
  classical
  rw [coeff_Θ J hΘ, coeff_inverseTransformDivisor_eq_zero (inverseTransformPrimeDivisor_ne_E J s),
    zero_add, Finset.sum_eq_single s (fun t _ hts => Finsupp.single_eq_of_ne
      (J.injective.ne hts.symm)) (by simp)]
  simp

/-- At a non-exceptional prime divisor `F` of `Y`, `p` is an isomorphism at the generic point of
`F`, so the discrepancy of `(Y, p, F)` is minus the coefficient of `p⁻¹_* B` along `F`. -/
private theorem isDiscrepancy_of_notMem_range (J : CrepantJunction sX B I) (n : ℕ)
    (K : Divisor X) (hK : K.IsCanonicalDivisor sX n) (F : MMP.Mori.PrimeDivisor J.Y)
    (hF : F ∉ Set.range J.E) :
    IsDiscrepancy sX n K B (divisorOver J F) (-(J.Θ.coeff F)) := by
  classical
  obtain ⟨c, ⟨hX, hK', m, hm, hC, -⟩⟩ :=
    MMP.Positivity.IsPair.exists_isDiscrepancy J.isKltPair.1.isPair hK (divisorOver J F)
  obtain ⟨D, hDc, hD⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
    ⟨hX, hK', m, by exact_mod_cast hm.ne', hC⟩ (divisorOver J F)
    (fun h => hF ((J.isExceptional_iff F).mp h))
  rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hDc
  have hη : J.p F.genericPoint = D.genericPoint := (inseparable_iff_closure_eq.mpr hDc).eq
  have := isProper_p J
  have hbir : D.genericPoint ∈ biregularLocus J.p := by
    refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one J.isKltPair.1.isPair.1 J.p
      J.isQFactorial.1.1 J.isBirationalMorphism ?_
    rw [ringKrullDim_stalk_eq_coheight, D.coheight_genericPoint]
    simp
  obtain ⟨a, -, hΘ⟩ := J.Θ_eq
  rwa [coeff_Θ J hΘ, coeff_inverseTransformDivisor_of_eq_some
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη
      (hη ▸ hbir)),
    Finset.sum_eq_zero fun s _ => Finsupp.single_eq_of_ne fun h => hF ⟨s, h.symm⟩,
    add_zero]

/-- `Θ` is the crepant boundary of `(X, B)` on `Y`. -/
private theorem isCrepantBoundary (J : CrepantJunction sX B I) (n : ℕ) (K : Divisor X)
    (hK : K.IsCanonicalDivisor sX n) :
    IsCrepantBoundary sX n K B J.p J.isQFactorial.1 J.isBirationalMorphism J.Θ := by
  intro F
  by_cases hF : F ∈ Set.range J.E
  swap
  · exact isDiscrepancy_of_notMem_range J n K hK F hF
  obtain ⟨s, rfl⟩ := hF
  obtain ⟨a, ha, hΘ⟩ := J.Θ_eq
  obtain ⟨c, hc⟩ :=
    MMP.Positivity.IsPair.exists_isDiscrepancy J.isKltPair.1.isPair hK (divisorOver J (J.E s))
  have hac : (a s : ℝ) = 1 + c := IsValuationLogDiscrepancy.unique (ha s) ⟨n, _, isProper_p J,
    J.valuation_eq s, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (isProper_p J)⟩
  have : -(J.Θ.coeff (J.E s)) = c := by
    rw [coeff_Θ_E J hΘ, show a s = 1 + c by exact_mod_cast hac]; ring
  exact this ▸ hc

/-- The composite `(W, g ≫ p, F)` over `X` of a proper divisor `(W, g, F)` over the source `Y` of a
junction, a proper divisor whose valuation restricts that of `(W, g, F)` along `p^*`. -/
private theorem exists_comp_divisorOver (J : CrepantJunction sX B I)
    (D : DivisorOver ℂ (J.p ≫ sX)) (hD : IsProper D.f) :
    haveI := J.isBirationalMorphism.isDominant
    ∃ E : DivisorOver ℂ sX, IsProper E.f ∧
      E.valuation = D.valuation.comap (functionFieldMap J.p) := by
  have := J.isBirationalMorphism.isDominant
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := isProper_p J
  have hb : IsBirationalMorphism (D.f ≫ J.p) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational J.p D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism J.isBirationalMorphism)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  have hY : IsNormalVariety ℂ ((D.f ≫ J.p) ≫ sX) := by
    rw [Category.assoc]; exact D.isNormalVariety
  refine ⟨⟨D.Y, D.f ≫ J.p, hY, hb, D.E⟩, (inferInstance : IsProper (D.f ≫ J.p)), ?_⟩
  have : IsDominant (D.f ≫ J.p) := hb.isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ J.p) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap J.p t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- Log discrepancies of `(Y, Θ)` and `(X, B)` agree. -/
private theorem isValuationLogDiscrepancy_iff (J : CrepantJunction sX B I)
    (ξ : Valuation J.Y.functionField (WithZero (Multiplicative ℤ))) (a : ℝ) :
    haveI := J.isBirationalMorphism.isDominant
    IsValuationLogDiscrepancy (J.p ≫ sX) J.Θ ξ a ↔
      IsValuationLogDiscrepancy sX B (ξ.comap (functionFieldMap J.p)) a := by
  have := J.isBirationalMorphism.isDominant
  have hPX : MMP.Mori.IsPair sX B := J.isKltPair.1.isPair
  obtain ⟨-, nX, KX, hKX, -⟩ := id hPX
  obtain rfl := eq_three_of_topologicalKrullDim_eq hKX.topologicalKrullDim_eq J.dim_base
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_Y J
  obtain ⟨hPY, hinv⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hPX J.p J.isQFactorial.1
    J.isBirationalMorphism hKX hKY (Or.inl (isCrepantBoundary J 3 KX hKX))
  constructor
  · rintro ⟨n, D, hDp, rfl, hDa⟩
    obtain rfl := eq_three_of_topologicalKrullDim_eq
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hDa) J.dim_eq
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPY hKY D
    obtain ⟨-, rfl⟩ := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc a).mp hDa
    obtain ⟨E, hEp, hEv⟩ := exists_comp_divisorOver J D hDp
    exact ⟨3, E, hEp, hEv, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
      ((hinv D E hEv c).mp hc) hEp⟩
  · rintro ⟨n, D', hD'p, hD'v, hD'a⟩
    obtain rfl := eq_three_of_topologicalKrullDim_eq
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD'a) J.dim_base
    obtain ⟨D, hDp, rfl⟩ := exists_properDivisorOver_valuation_eq_of_comap_eq (sZ := sX)
      J.isQFactorial.1 (𝟙 X) J.p (isBirationalMorphism_of_isIso _) J.isBirationalMorphism
      (isProper_p J) (Category.id_comp _) rfl D' ξ (by ext t; simp [hD'v])
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPY hKY D
    obtain ⟨-, rfl⟩ := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy
      ((hinv D D' hD'v c).mp hc) a).mp hD'a
    exact ⟨3, D, hDp, rfl, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDp⟩

/-- **Crepant junctions are crepant.** For a crepant junction `(p, Θ)` of `(X, B)` extracting
`I`, `(Y, Θ)` is a pair (`K_Y + Θ` is `ℚ`-Cartier), `K_Y + Θ = p^*(K_X + B)` (for every canonical
divisor `K` of `X`, `Θ` is the crepant boundary of `(X, B)` on `Y`), and
`a(ξ; Y, Θ) = a(ξ ∘ p^*; X, B)` for every valuation `ξ` of `k(Y)`. -/
@[mmp "lem_mmp_indexc_junction_crepant"]
public theorem CrepantJunction.isCrepant (J : CrepantJunction sX B I) :
    haveI := J.isBirationalMorphism.isDominant
    IsPair (J.p ≫ sX) J.Θ ∧
      (∀ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX n →
        IsCrepantBoundary sX n K B J.p J.isQFactorial.1 J.isBirationalMorphism J.Θ) ∧
      ∀ (ξ : Valuation J.Y.functionField (WithZero (Multiplicative ℤ))) (a : ℝ),
        IsValuationLogDiscrepancy (J.p ≫ sX) J.Θ ξ a ↔
          IsValuationLogDiscrepancy sX B (ξ.comap (functionFieldMap J.p)) a :=
  ⟨isPair J, isCrepantBoundary J, isValuationLogDiscrepancy_iff J⟩

end MMP.Fourfold
