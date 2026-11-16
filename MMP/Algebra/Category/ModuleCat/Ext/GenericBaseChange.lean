module

import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.RingTheory.RegularLocalRing.QuotientRegularIff
public import MMP.AlgebraicGeometry.Singularities.Semismooth.SingularLocus
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.ExcellentStalks
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverSideConditions
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocusCodimensionZero

/-!
# Generic base change of `Ext`, divisorial valuations, and the semismooth conductor

This file collects three foundational results of the minimal model program.

**Generic base change of `Ext` into a polynomial ring.** Let `R` be a regular domain of finite
type over a field `k`, `P = R[x_σ]` a polynomial ring in finitely many variables and `A = P ⧸ I`.
After inverting one nonzero `f : R`, the algebra `A` is flat over `R`, and for every prime `s` of
`R` with `f ∉ s` the canonical comparison map
`P_s ⊗_P Ext^i_P(A, P) → Ext^i_{P_s}(P_s ⊗_P A, P_s ⊗_P P)`, where `P_s = κ(s)[x_σ]`, is an
isomorphism; moreover all these modules vanish beyond a uniform degree `N`.

**Valuations of maximal residue dimension are divisorial.** A normalized discrete valuation `v`
of the function field `K` of a variety `X` over `k`, trivial on `k`, whose residue field has
transcendence degree `trdeg_k K - 1` and which has a centre on `X`, is the valuation of a prime
divisor on a normal variety `Y` with a proper birational morphism `Y ⟶ X`.

**The conductor equalizer of a semismooth surface.** Let `S` be a semismooth complex surface,
`ν : S^ν ⟶ S` its normalization, `D` its reduced singular locus, `D^ν = ν⁻¹(D)` with its reduced
structure, `π : D^ν ⟶ D` the induced double cover and `τ` its covering involution. Then a section
of `𝒪_{S^ν}` over `ν⁻¹U` comes from `𝒪_S(U)` if and only if its restriction to `D^ν` is
`τ`-invariant: `𝒪_S` is the fibre product `ν_*𝒪_{S^ν} ×_{ν_*𝒪_{D^ν}} 𝒪_D`.

## Main results

* `MMP.Foundations.exists_ne_zero_flat_and_ext_baseChange`: generic flatness of `A` together with
  the base change isomorphism for `Ext^i_P(A, P)` over the fibres of `Spec R`.
* `MMP.Mori.DivisorOver.exists_isProper_valuation_eq_of_trdeg_residueField`: a discrete valuation
  of maximal residue transcendence degree with a centre on `X` is divisorial over `X`.
* `MMP.Flips.IsSemismooth.mem_range_normalization_app_iff`: the image of
  `Γ(S, U) → Γ(S^ν, ν⁻¹U)` is the set of sections whose restriction to `D^ν` is `τ`-invariant.

## Implementation notes

*Base change of `Ext`.* The fibre `A ⊗_R κ(s)` is written as the extension of scalars `P_s ⊗_P A`
along `MvPolynomial.map (algebraMap R κ(s))`, and likewise for `Ext^i_P(A, P)`; both agree with the
tensor products over `R` since `P_s = P ⊗_R κ(s)`. Inverting `f` is expressed by restricting to
the primes `s` with `f ∉ s` and by flatness of `A_f` over `R`. The comparison isomorphism `e` is
pinned by its characterising property: restricting `e (1 ⊗ x)` along `P → P_s` and pulling back
along the unit `A → P_s ⊗_P A` gives the image of `x` under the unit `P → P_s ⊗_P P`.

The vanishing comes from finite global dimension: `P` and `κ(s)[x_σ]` are regular of finite Krull
dimension. The base change is proved by induction along a resolution of `A` by syzygy sequences
`0 → K → F → M → 0` with `F` finite free. Writing `φ : P → Q` for the base change, adjunction gives
`Ext^i_Q(φ^* M, N) ≅ Ext^i_P(M, φ_* N)` as soon as `φ^*` keeps every syzygy sequence of `M` short
exact; generic freeness over `R` of `M`, of the image of `Hom(F, P) → Hom(K, P)` and of
`Ext^1(M, P)` provides this after inverting one `f`. The comparison map is then bijective by the
five lemma, starting from finite free modules in degree zero.

*Divisorial valuations.* The function field is `X.functionField` with the `k`-algebra structure
`MMP.Mori.functionFieldAlgebra`; the residue field of `v` is
`IsLocalRing.ResidueField v.valuationSubring`, a `k`-algebra because `v` is trivial on `k`. The
transcendence degree condition is `trdeg_k κ(v) + 1 = trdeg_k K`. The proof lifts a transcendence
basis `u_1, …, u_m` of `κ(v)` to the valuation ring, writes `u_j = a_j / s` on an affine
neighbourhood of the centre, and blows up `(s, a_1, …, a_m)`; on the normalization `Y` of the
blow-up, the centre `y` of `v` has `u_j ∈ 𝒪_{Y,y}`, so `κ(y)` has transcendence degree at least
`m`, whence `dim 𝒪_{Y,y} ≤ 1` and `y` is the generic point of a prime divisor.

*The conductor.* The covering involution is not constructed: `τ : D^ν ⟶ D^ν` is a morphism over
`D` with `τ ∘ τ = 1` such that on every open `V ⊆ D` the sections of `𝒪_D` are exactly the
`τ`-invariant sections of `π_*𝒪_{D^ν}`, which characterises it; `π` is given by
`π ≫ ι_D = ι_{D^ν} ≫ ν`, which determines it since `ι_D` is a monomorphism. A section is
`τ`-invariant when it agrees with its `τ`-pullback on every open of `W ∩ τ⁻¹W`. The singular locus
is the complement of `MMP.Mori.smoothLocus sX`. The forward direction holds because `τ ≫ π = π`.
For the converse, a section vanishing on `D^ν` comes from `𝒪_S` (the ideal of `D^ν` is the
conductor); this is checked on the completed local rings at closed points, which are the double
normal crossing `ℂ⟦x, y, z⟧ ⧸ (xy)` or the pinch point `ℂ⟦x, y, z⟧ ⧸ (x² - yz²)`, and descends
along the faithfully flat completion.

## References

* [Kollár, Mori, *Birational geometry of algebraic varieties*][KM98]
* [Kollár, *Flips and abundance for algebraic threefolds*, 12.2][FA]
-/

universe u

namespace MMP.Foundations

open CategoryTheory Abelian Limits TensorProduct

/-- Over a Noetherian regular ring of finite Krull dimension `n` every module has projective
dimension `≤ n`. -/
private theorem hasProjectiveDimensionLT_of_ringKrullDim_eq {S : Type u} [CommRing S]
    [IsNoetherianRing S] [IsRegularRing S] (n : ℕ) (hn : ringKrullDim S = n)
    (M : ModuleCat.{u} S) : HasProjectiveDimensionLT M (n + 1) := by
  have h12 := (isRegularRing_tfae (R := S) n).out 1 2
  have hgl : (⨆ M : ModuleCat.{u} S, projectiveDimension M) = (n : WithBot ℕ∞) :=
    h12.mpr ⟨‹IsRegularRing S›, hn⟩
  exact (projectiveDimension_le_iff M n).mp
    (hgl ▸ le_iSup (fun M : ModuleCat.{u} S => projectiveDimension M) M)

/-- A Noetherian regular ring of finite Krull dimension `n` has global dimension `≤ n`, so every
`Ext^i` out of any module vanishes for `n < i`. -/
private theorem subsingleton_ext_of_ringKrullDim_eq {S : Type u} [CommRing S]
    [IsNoetherianRing S] [IsRegularRing S] (n : ℕ) (hn : ringKrullDim S = n)
    (M N : ModuleCat.{u} S) (i : ℕ) (hi : n < i) : Subsingleton (Abelian.Ext M N i) :=
  have := hasProjectiveDimensionLT_of_ringKrullDim_eq n hn M
  HasProjectiveDimensionLT.subsingleton M (n + 1) i (by omega) N

/-- The Krull dimension of a finite-type algebra over a field is a natural number. -/
private theorem exists_ringKrullDim_eq_of_finiteType (k : Type u) [Field k] (S : Type u)
    [CommRing S] [Nontrivial S] [Algebra k S] [Algebra.FiniteType k S] :
    ∃ n : ℕ, ringKrullDim S = n := by
  obtain ⟨m, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k S›
  have hle : ringKrullDim S ≤ m := by
    have := ringKrullDim_le_of_surjective g.toRingHom hg
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      ENat.card_eq_coe_fintype_card, Fintype.card_fin, zero_add] at this
  have hge : 0 ≤ ringKrullDim S := ringKrullDim_nonneg_of_nontrivial
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp
      (ne_bot_of_le_ne_bot (WithBot.coe_ne_bot (a := (0 : ℕ∞))) hge)
  rw [← hd] at hle
  have hd' : d ≤ (m : ℕ∞) := by exact_mod_cast hle
  lift d to ℕ using (lt_of_le_of_lt hd' (ENat.coe_lt_top m)).ne
  exact ⟨d, hd.symm⟩

/-- **Generic flatness of a finite-type algebra over a domain**: there is a nonzero `f` with
`S_f` flat over `R`. -/
private theorem exists_ne_zero_flat_localizationAway {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ f : R, f ≠ 0 ∧ Module.Flat R (Localization.Away (algebraMap R S f)) := by
  obtain ⟨U, -, hU, hgood⟩ :=
    Algebra.exists_isOpen_dense_isFinitePresentationFreeAway (R := R) (S := S) (M := S)
  obtain ⟨u, hu⟩ := hU.nonempty
  obtain ⟨f, hfu, -, hf⟩ := hgood u hu
  refine ⟨f, ?_, ?_⟩
  · rintro rfl
    simp at hfu
  · have hfree := hf.2.2.1
    have : Module.Flat R (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))) :=
      Module.Flat.trans R (Localization.Away f) _
    rwa [Algebra.algebraMapSubmonoid_powers] at this

/-- Flatness of `S_g` over `R` passes to every further localization `S_{fg}`. -/
private theorem flat_localizationAway_mul {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f g : S) [Module.Flat R (Localization.Away g)] :
    Module.Flat R (Localization.Away (f * g)) := by
  let T := Localization.Away (algebraMap S (Localization.Away g) f)
  have : IsLocalization.Away (f * g) T := IsLocalization.Away.mul (Localization.Away g) T g f
  have : Module.Flat R T := Module.Flat.trans R (Localization.Away g) T
  let e : Localization.Away (f * g) ≃ₐ[S] T :=
    IsLocalization.algEquiv (Submonoid.powers (f * g)) _ _
  exact Module.Flat.of_linearEquiv (e.toLinearEquiv.restrictScalars R)

section ExtAdjunction

variable {P Q : Type u} [CommRing P] [CommRing Q] (φ : P →+* Q)

private noncomputable def Ψ (M : ModuleCat.{u} P) (N : ModuleCat.{u} Q) (i : ℕ) :
    Ext ((ModuleCat.extendScalars φ).obj M) N i →+ Ext M ((ModuleCat.restrictScalars φ).obj N) i :=
  AddMonoidHom.comp
    ((Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M)).precomp
      ((ModuleCat.restrictScalars φ).obj N) (zero_add i))
    ((ModuleCat.restrictScalars φ).mapExtAddHom ((ModuleCat.extendScalars φ).obj M) N i)

private lemma Ψ_apply (M : ModuleCat.{u} P) (N : ModuleCat.{u} Q) (i : ℕ) (y) :
    Ψ φ M N i y = (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M)).comp
      (y.mapExactFunctor (ModuleCat.restrictScalars φ)) (zero_add i) := rfl

private lemma Ψ_precomp {M M' : ModuleCat.{u} P} (N : ModuleCat.{u} Q) (g : M ⟶ M') {i : ℕ}
    (y : Ext ((ModuleCat.extendScalars φ).obj M') N i) :
    Ψ φ M N i ((Ext.mk₀ ((ModuleCat.extendScalars φ).map g)).comp y (zero_add i)) =
      (Ext.mk₀ g).comp (Ψ φ M' N i y) (zero_add i) := by
  rw [Ψ_apply, Ψ_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀]
  all_goals simp

/-- the unit as a morphism of short complexes -/
private noncomputable def unitHom (S : ShortComplex (ModuleCat.{u} P)) :
    S ⟶ (S.map (ModuleCat.extendScalars φ)).map (ModuleCat.restrictScalars φ) where
  τ₁ := (ModuleCat.extendRestrictScalarsAdj φ).unit.app S.X₁
  τ₂ := (ModuleCat.extendRestrictScalarsAdj φ).unit.app S.X₂
  τ₃ := (ModuleCat.extendRestrictScalarsAdj φ).unit.app S.X₃
  comm₁₂ := ((ModuleCat.extendRestrictScalarsAdj φ).unit.naturality S.f).symm
  comm₂₃ := ((ModuleCat.extendRestrictScalarsAdj φ).unit.naturality S.g).symm

private lemma Ψ_extClass {S : ShortComplex (ModuleCat.{u} P)} (hS : S.ShortExact)
    (hS' : (S.map (ModuleCat.extendScalars φ)).ShortExact) (N : ModuleCat.{u} Q) {i j : ℕ}
    (h : 1 + i = j)
    (y : Ext ((ModuleCat.extendScalars φ).obj S.X₁) N i) :
    Ψ φ S.X₃ N j (hS'.extClass.comp y h) = hS.extClass.comp (Ψ φ S.X₁ N i y) h := by
  have key := ShortComplex.ShortExact.extClass_naturality hS
    (hS'.map_of_exact (ModuleCat.restrictScalars φ)) (unitHom φ S)
  rw [Ψ_apply, Ψ_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  have e1 := Ext.comp_assoc hS.extClass (Ext.mk₀ (unitHom φ S).τ₁)
    (y.mapExactFunctor (ModuleCat.restrictScalars φ)) (add_zero 1) (zero_add i) h (a := j)
  have e2 := Ext.comp_assoc (Ext.mk₀ (unitHom φ S).τ₃) (hS'.map_of_exact
    (ModuleCat.restrictScalars φ)).extClass
    (y.mapExactFunctor (ModuleCat.restrictScalars φ)) (zero_add 1) h (by omega) (a := j)
  rw [key] at e1
  exact e2.symm.trans e1

private lemma Ψ_mk₀ (M : ModuleCat.{u} P) (N : ModuleCat.{u} Q)
    (g : (ModuleCat.extendScalars φ).obj M ⟶ N) :
    Ψ φ M N 0 (Ext.mk₀ g) =
      Ext.mk₀ (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N) g) := by
  rw [Ψ_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  simp [Adjunction.homEquiv_unit]

private lemma Ψ_zero_bijective (M : ModuleCat.{u} P) (N : ModuleCat.{u} Q) :
    Function.Bijective (Ψ φ M N 0) := by
  have h : Ψ φ M N 0 ∘ Ext.mk₀ =
      Ext.mk₀ ∘ ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N) := by
    funext g; exact Ψ_mk₀ φ M N g
  have h2 : Function.Bijective (Ψ φ M N 0 ∘ Ext.mk₀) := by
    rw [h]; exact (Ext.mk₀_bijective _ _).comp (Equiv.bijective _)
  exact (Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective _ _)).1 h2

private lemma Ψ_proj_bijective (F : ModuleCat.{u} P) [Projective F]
    [Projective ((ModuleCat.extendScalars φ).obj F)] (N : ModuleCat.{u} Q) (n : ℕ) :
    Function.Bijective (Ψ φ F N n) := by
  cases n with
  | zero => exact Ψ_zero_bijective φ F N
  | succ n =>
    have : Subsingleton (Ext F ((ModuleCat.restrictScalars φ).obj N) (n + 1)) :=
      Ext.subsingleton_of_projective _ _ _
    have : Subsingleton (Ext ((ModuleCat.extendScalars φ).obj F) N (n + 1)) :=
      Ext.subsingleton_of_projective _ _ _
    exact Function.bijective_of_subsingleton' _

private lemma shortExact_map_ex {S : ShortComplex (ModuleCat.{u} P)} (hS : S.ShortExact)
    (hm : Mono ((ModuleCat.extendScalars φ).map S.f)) :
    (S.map (ModuleCat.extendScalars φ)).ShortExact := by
  have : Epi S.g := hS.epi_g
  have he : Epi ((ModuleCat.extendScalars φ).map S.g) := inferInstance
  exact { exact := hS.exact.map_of_epi_of_preservesCokernel (ModuleCat.extendScalars φ) hS.epi_g
            inferInstance
          mono_f := hm
          epi_g := he }

private lemma projective_ex (M : ModuleCat.{u} P) [Projective M] :
    Projective ((ModuleCat.extendScalars φ).obj M) :=
  (ModuleCat.extendRestrictScalarsAdj φ).map_projective M inferInstance

/-- Conditions on a class `C` of `P`-modules making `φ^*` behave on syzygies. -/
private structure GoodClass (C : ModuleCat.{u} P → Prop) : Prop where
  mono : ∀ S : ShortComplex (ModuleCat.{u} P), S.ShortExact → C S.X₃ →
    Mono ((ModuleCat.extendScalars φ).map S.f)
  syz : ∀ S : ShortComplex (ModuleCat.{u} P), S.ShortExact → Projective S.X₂ → C S.X₃ → C S.X₁

/-- The presentation sequence of a module. -/
private noncomputable def presSeq (M : ModuleCat.{u} P) : ShortComplex (ModuleCat.{u} P) :=
  ShortComplex.mk (kernel.ι (Classical.arbitrary (ProjectivePresentation M)).f)
    (Classical.arbitrary (ProjectivePresentation M)).f (kernel.condition _)

private lemma presSeq_shortExact (M : ModuleCat.{u} P) : (presSeq M).ShortExact :=
  { exact := ShortComplex.exact_kernel _
    mono_f := equalizer.ι_mono
    epi_g := (Classical.arbitrary (ProjectivePresentation M)).epi }

private lemma presSeq_X₂ (M : ModuleCat.{u} P) : Projective (presSeq M).X₂ :=
  (Classical.arbitrary (ProjectivePresentation M)).projective

private theorem Ψ_bijective {C : ModuleCat.{u} P → Prop} (hC : GoodClass φ C) (N : ModuleCat.{u} Q)
    (n : ℕ) : ∀ M : ModuleCat.{u} P, C M → Function.Bijective (Ψ φ M N n) := by
  induction n with
  | zero => intro M _; exact Ψ_zero_bijective φ M N
  | succ n ih =>
    intro M hM
    let S := presSeq M
    have hS : S.ShortExact := presSeq_shortExact M
    have hSX2 : Projective S.X₂ := presSeq_X₂ M
    have hm := hC.mono S hS hM
    have hS' := shortExact_map_ex φ hS hm
    have hK : C S.X₁ := hC.syz S hS hSX2 hM
    have : Projective ((ModuleCat.extendScalars φ).obj S.X₂) := projective_ex φ _
    have h1 : Function.Surjective (Ψ φ S.X₂ N n) := (Ψ_proj_bijective φ S.X₂ N n).2
    have h2 := ih _ hK
    have hex1 := (ShortComplex.ab_exact_iff_function_exact _).1
      (Ext.contravariant_sequence_exact₁' hS' N n (n + 1) (add_comm 1 n))
    have hex2 := (ShortComplex.ab_exact_iff_function_exact _).1
      (Ext.contravariant_sequence_exact₁' hS ((ModuleCat.restrictScalars φ).obj N) n (n + 1)
        (add_comm 1 n))
    have hs1 : Subsingleton (Ext ((ModuleCat.extendScalars φ).obj S.X₂) N (n + 1)) :=
      Ext.subsingleton_of_projective _ _ _
    have hs1' : Subsingleton (Ext (S.map (ModuleCat.extendScalars φ)).X₂ N (n + 1)) := hs1
    have hs2 : Subsingleton (Ext S.X₂ ((ModuleCat.restrictScalars φ).obj N) (n + 1)) :=
      Ext.subsingleton_of_projective _ _ _
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Ext.mk₀ (S.map (ModuleCat.extendScalars φ)).f).precomp N (zero_add n))
      (hS'.extClass.precomp N (add_comm 1 n))
      ((Ext.mk₀ S.f).precomp ((ModuleCat.restrictScalars φ).obj N) (zero_add n))
      (hS.extClass.precomp ((ModuleCat.restrictScalars φ).obj N) (add_comm 1 n))
      (Ψ φ S.X₂ N n) (Ψ φ S.X₁ N n) (Ψ φ S.X₃ N (n + 1)) ?_ ?_ hex1 hex2 h1 h2 ?_ ?_
    · exact AddMonoidHom.ext fun y => (Ψ_precomp φ N S.f y).symm
    · exact AddMonoidHom.ext fun y => (Ψ_extClass φ hS hS' N (add_comm 1 n) y).symm
    · intro x
      exact Ext.contravariant_sequence_exact₃ hS' N x (Subsingleton.elim _ _) (add_comm 1 n)
    · intro x
      exact Ext.contravariant_sequence_exact₃ hS _ x (Subsingleton.elim _ _) (add_comm 1 n)

/-- The unit, as a map into the extended module. -/
private noncomputable def unitE (X : ModuleCat.{u} P) (x : X) : (ModuleCat.extendScalars φ).obj X :=
  (ModuleCat.extendRestrictScalarsAdj φ).unit.app X x

/-- Two morphisms out of an extended module agreeing on the unit are equal. -/
private lemma hom_ext_unit {X : ModuleCat.{u} P} {Z : ModuleCat.{u} Q}
    {g₁ g₂ : (ModuleCat.extendScalars φ).obj X ⟶ Z}
    (h : ∀ x : X, g₁.hom (unitE φ X x) = g₂.hom (unitE φ X x)) : g₁ = g₂ := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv X Z).injective
  simp only [Adjunction.homEquiv_unit]
  ext x
  exact h x

private lemma Ψ_smul (M : ModuleCat.{u} P) (N : ModuleCat.{u} Q) (i : ℕ) (a : P)
    (y : Ext ((ModuleCat.extendScalars φ).obj M) N i) :
    Ψ φ M N i (φ a • y) = a • Ψ φ M N i y := by
  rw [Ext.smul_eq_comp_mk₀ y (φ a), Ext.smul_eq_comp_mk₀ (Ψ φ M N i y) a, Ψ_apply, Ψ_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]
  congr 2

/-- Push forward along the unit of the target. -/
private noncomputable def Θ (Y M : ModuleCat.{u} P) (i : ℕ) :
    Ext M Y i →ₗ[P] Ext M
        ((ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj Y)) i :=
  (Ext.bilinearCompOfLinear P M Y
      ((ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj Y))
    i 0 i (add_zero i)).flip (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj φ).unit.app Y))

private lemma Θ_apply (Y M : ModuleCat.{u} P) (i : ℕ) (x : Ext M Y i) :
    Θ φ Y M i x = x.comp (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj φ).unit.app Y))
      (add_zero i) := rfl

/-- The `P`-module `Ext^i_P(M, Y)`. -/
private noncomputable abbrev EP (Y M : ModuleCat.{u} P) (i : ℕ) : ModuleCat.{u} P :=
  ModuleCat.of P (Ext M Y i)

/-- The `Q`-module `Ext^i_Q(φ^* M, φ^* Y)`. -/
private noncomputable abbrev EQ (Y M : ModuleCat.{u} P) (i : ℕ) : ModuleCat.{u} Q :=
  ModuleCat.of Q (Ext ((ModuleCat.extendScalars φ).obj M) ((ModuleCat.extendScalars φ).obj Y) i)

/-- The inverse of `Ψ` composed with `Θ`, as a semilinear map. -/
private noncomputable def εLin (Y M : ModuleCat.{u} P) (i : ℕ)
    (hΨ : Function.Bijective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i)) :
    EP Y M i ⟶ (ModuleCat.restrictScalars φ).obj (EQ φ Y M i) :=
  ConcreteCategory.ofHom
    { toFun := fun x => (AddEquiv.ofBijective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i) hΨ).symm
        (Θ φ Y M i x)
      map_add' := fun x y => by rw [map_add, map_add]; rfl
      map_smul' := fun a x => by
        apply (AddEquiv.ofBijective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i) hΨ).injective
        have h := Ψ_smul φ M ((ModuleCat.extendScalars φ).obj Y) i a
          ((AddEquiv.ofBijective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i) hΨ).symm
            (Θ φ Y M i x))
        have h2 : ∀ z, Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i
            ((AddEquiv.ofBijective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i) hΨ).symm z) = z :=
          fun z => (AddEquiv.ofBijective
              (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i) hΨ).apply_symm_apply z
        change Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i _ = Ψ φ M
            ((ModuleCat.extendScalars φ).obj Y) i (φ a • _)
        rw [h2, h, h2, map_smul] }

/-- The comparison map `φ^* Ext^i_P(M,Y) → Ext^i_Q(φ^* M, φ^* Y)`. -/
private noncomputable def eMap (Y M : ModuleCat.{u} P) (i : ℕ)
    (hΨ : Function.Bijective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i)) :
    (ModuleCat.extendScalars φ).obj (EP Y M i) ⟶ EQ φ Y M i :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv (EP Y M i) (EQ φ Y M i)).symm
    (εLin φ Y M i hΨ)

/-- The characterising property of the comparison map. -/
private def IsE (Y M : ModuleCat.{u} P) (i : ℕ)
    (e : (ModuleCat.extendScalars φ).obj (EP Y M i) ⟶ EQ φ Y M i) : Prop :=
  ∀ x : Ext M Y i, Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i
    (e.hom (unitE φ (EP Y M i) x)) = Θ φ Y M i x

private lemma eMap_isE (Y M : ModuleCat.{u} P) (i : ℕ)
    (hΨ : Function.Bijective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i)) :
    IsE φ Y M i (eMap φ Y M i hΨ) := by
  intro x
  have : (eMap φ Y M i hΨ).hom (unitE φ (EP Y M i) x) =
      (AddEquiv.ofBijective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i) hΨ).symm
        (Θ φ Y M i x) := by
    have h := congrArg (fun g => g.hom x) ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv_unit
      (f := eMap φ Y M i hΨ))
    simp only [eMap, Equiv.apply_symm_apply] at h
    exact h.symm
  rw [this]
  exact (AddEquiv.ofBijective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i) hΨ).apply_symm_apply _

private lemma extendScalars_map_unitE {A B : ModuleCat.{u} P} (f : A ⟶ B) (x : A) :
    ((ModuleCat.extendScalars φ).map f).hom (unitE φ A x) = unitE φ B (f.hom x) :=
  congrArg (fun g => g.hom x) ((ModuleCat.extendRestrictScalarsAdj φ).unit.naturality f)

/-- Precomposition with a morphism, on `Ext` into `Y`, `P`-linear. -/
private noncomputable def precompP (Y : ModuleCat.{u} P) {M M' : ModuleCat.{u} P} (g : M ⟶ M')
    (i : ℕ) :
    EP Y M' i ⟶ EP Y M i :=
  ModuleCat.ofHom (Ext.precompOfLinear (Ext.mk₀ g) P Y (zero_add i))

/-- Precomposition with a morphism, on `Ext` into `φ^* Y`, `Q`-linear. -/
private noncomputable def precompQ (Y : ModuleCat.{u} P) {M M' : ModuleCat.{u} P} (g : M ⟶ M')
    (i : ℕ) :
    EQ φ Y M' i ⟶ EQ φ Y M i :=
  ModuleCat.ofHom (Ext.precompOfLinear (Ext.mk₀ ((ModuleCat.extendScalars φ).map g)) Q
    ((ModuleCat.extendScalars φ).obj Y) (zero_add i))

private lemma precompP_apply (Y : ModuleCat.{u} P) {M M' : ModuleCat.{u} P} (g : M ⟶ M') (i : ℕ)
    (z : Ext M' Y i) : (precompP Y g i).hom z = (Ext.mk₀ g).comp z (zero_add i) := rfl

private lemma precompQ_apply (Y : ModuleCat.{u} P) {M M' : ModuleCat.{u} P} (g : M ⟶ M') (i : ℕ)
    (z : Ext ((ModuleCat.extendScalars φ).obj M') ((ModuleCat.extendScalars φ).obj Y) i) :
    (precompQ φ Y g i).hom z =
      (Ext.mk₀ ((ModuleCat.extendScalars φ).map g)).comp z (zero_add i) := rfl

private lemma e_natural (Y : ModuleCat.{u} P) {M M' : ModuleCat.{u} P} (g : M ⟶ M') (i : ℕ)
    (hM : Function.Injective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i))
    {e : (ModuleCat.extendScalars φ).obj (EP Y M i) ⟶ EQ φ Y M i} (he : IsE φ Y M i e)
    {e' : (ModuleCat.extendScalars φ).obj (EP Y M' i) ⟶ EQ φ Y M' i} (he' : IsE φ Y M' i e') :
    (ModuleCat.extendScalars φ).map (precompP Y g i) ≫ e = e' ≫ precompQ φ Y g i := by
  apply hom_ext_unit φ
  intro x
  apply hM
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [extendScalars_map_unitE, he, precompQ_apply, Ψ_precomp, he' x, precompP_apply]
  simp only [Θ_apply]
  exact Ext.comp_assoc (Ext.mk₀ g) x (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj φ).unit.app Y))
    (zero_add i) (add_zero i) (by omega)

/-- The connecting map on `Ext^•(-, Y)`, `P`-linear. -/
private noncomputable def δP (Y : ModuleCat.{u} P) {S : ShortComplex (ModuleCat.{u} P)}
    (hS : S.ShortExact)
    {i j : ℕ} (h : 1 + i = j) : EP Y S.X₁ i ⟶ EP Y S.X₃ j :=
  ModuleCat.ofHom (Ext.precompOfLinear hS.extClass P Y h)

/-- The connecting map on `Ext^•(φ^* -, φ^* Y)`, `Q`-linear. -/
private noncomputable def δQ (Y : ModuleCat.{u} P) {S : ShortComplex (ModuleCat.{u} P)}
    (hS' : (S.map (ModuleCat.extendScalars φ)).ShortExact)
    {i j : ℕ} (h : 1 + i = j) : EQ φ Y S.X₁ i ⟶ EQ φ Y S.X₃ j :=
  ModuleCat.ofHom (Ext.precompOfLinear hS'.extClass Q ((ModuleCat.extendScalars φ).obj Y) h)

private lemma δP_apply (Y : ModuleCat.{u} P) {S : ShortComplex (ModuleCat.{u} P)}
    (hS : S.ShortExact)
    {i j : ℕ} (h : 1 + i = j) (z : Ext S.X₁ Y i) : (δP Y hS h).hom z = hS.extClass.comp z h := rfl

private lemma δQ_apply (Y : ModuleCat.{u} P) {S : ShortComplex (ModuleCat.{u} P)}
    (hS' : (S.map (ModuleCat.extendScalars φ)).ShortExact)
    {i j : ℕ} (h : 1 + i = j)
    (z : Ext ((ModuleCat.extendScalars φ).obj S.X₁) ((ModuleCat.extendScalars φ).obj Y) i) :
    (δQ φ Y hS' h).hom z = hS'.extClass.comp z h := rfl

private lemma e_delta (Y : ModuleCat.{u} P) {S : ShortComplex (ModuleCat.{u} P)} (hS : S.ShortExact)
    (hS' : (S.map (ModuleCat.extendScalars φ)).ShortExact) {i j : ℕ} (h : 1 + i = j)
    (h3 : Function.Injective (Ψ φ S.X₃ ((ModuleCat.extendScalars φ).obj Y) j))
    {e₁ : (ModuleCat.extendScalars φ).obj (EP Y S.X₁ i) ⟶ EQ φ Y S.X₁ i}
    (he₁ : IsE φ Y S.X₁ i e₁)
    {e₃ : (ModuleCat.extendScalars φ).obj (EP Y S.X₃ j) ⟶ EQ φ Y S.X₃ j}
    (he₃ : IsE φ Y S.X₃ j e₃) :
    (ModuleCat.extendScalars φ).map (δP Y hS h) ≫ e₃ = e₁ ≫ δQ φ Y hS' h := by
  apply hom_ext_unit φ
  intro x
  apply h3
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [extendScalars_map_unitE, he₃, δQ_apply, Ψ_extClass φ hS hS' ((ModuleCat.extendScalars φ).obj Y) h, he₁ x,
      δP_apply]
  simp only [Θ_apply]
  exact (Ext.comp_assoc hS.extClass x (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj φ).unit.app Y))
    h (add_zero i) (by omega))

section Exactness

variable {C : Type*} [Category C] [Abelian C] [HasExt C] {S : ShortComplex C} (hS : S.ShortExact)
  (Y : C)

include hS

private lemma exact_ext_a (n : ℕ) :
    Function.Exact ((Ext.mk₀ S.g).precomp Y (zero_add n) : Ext S.X₃ Y n → Ext S.X₂ Y n)
      ((Ext.mk₀ S.f).precomp Y (zero_add n) : Ext S.X₂ Y n → Ext S.X₁ Y n) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.contravariant_sequence_exact₂' hS Y n)

private lemma exact_ext_b {i j : ℕ} (h : 1 + i = j) :
    Function.Exact ((Ext.mk₀ S.f).precomp Y (zero_add i) : Ext S.X₂ Y i → Ext S.X₁ Y i)
      (hS.extClass.precomp Y h : Ext S.X₁ Y i → Ext S.X₃ Y j) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.contravariant_sequence_exact₁' hS Y i j h)

private lemma exact_ext_c {i j : ℕ} (h : 1 + i = j) :
    Function.Exact (hS.extClass.precomp Y h : Ext S.X₁ Y i → Ext S.X₃ Y j)
      ((Ext.mk₀ S.g).precomp Y (zero_add j) : Ext S.X₃ Y j → Ext S.X₂ Y j) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.contravariant_sequence_exact₃' hS Y i j h)

end Exactness

private lemma exact_ex {A B C : ModuleCat.{u} P} (f : A ⟶ B) (g : B ⟶ C) [Epi g]
    (h : Function.Exact f.hom g.hom) :
    Function.Exact ((ModuleCat.extendScalars φ).map f).hom
        ((ModuleCat.extendScalars φ).map g).hom := by
  have hz : f ≫ g = 0 := ModuleCat.hom_ext (LinearMap.ext fun x => h.apply_apply_eq_zero x)
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (.mk f g hz)).2 h
      ).map_of_epi_of_preservesCokernel (ModuleCat.extendScalars φ) inferInstance inferInstance)

private lemma δP_surj (Y : ModuleCat.{u} P) {S : ShortComplex (ModuleCat.{u} P)} (hS : S.ShortExact)
    (hF : Projective S.X₂) (k : ℕ) (h : 1 + k = k + 1) :
    Function.Surjective (δP Y hS h).hom := by
  have hs1 : Subsingleton (Ext S.X₂ Y (k + 1)) := Ext.subsingleton_of_projective _ _ _
  exact fun x => ((exact_ext_c hS Y h) x).1 (Subsingleton.elim _ _)

/-- The inductive step in positive degrees. -/
private lemma step_succ (Y : ModuleCat.{u} P) {S : ShortComplex (ModuleCat.{u} P)}
    (hS : S.ShortExact)
    (hS' : (S.map (ModuleCat.extendScalars φ)).ShortExact) (hF : Projective S.X₂) (k : ℕ)
    (hΨK : Function.Injective (Ψ φ S.X₁ ((ModuleCat.extendScalars φ).obj Y) k))
    (hΨM : Function.Injective (Ψ φ S.X₃ ((ModuleCat.extendScalars φ).obj Y) (k + 1)))
    {eF : (ModuleCat.extendScalars φ).obj (EP Y S.X₂ k) ⟶ EQ φ Y S.X₂ k}
    (heF : IsE φ Y S.X₂ k eF) (hsF : Function.Surjective eF.hom)
    {eK : (ModuleCat.extendScalars φ).obj (EP Y S.X₁ k) ⟶ EQ φ Y S.X₁ k}
    (heK : IsE φ Y S.X₁ k eK) (hbK : Function.Bijective eK.hom)
    {eM : (ModuleCat.extendScalars φ).obj (EP Y S.X₃ (k + 1)) ⟶ EQ φ Y S.X₃ (k + 1)}
    (heM : IsE φ Y S.X₃ (k + 1) eM) : Function.Bijective eM.hom := by
  have h : 1 + k = k + 1 := add_comm 1 k
  have : Projective ((ModuleCat.extendScalars φ).obj S.X₂) := projective_ex φ _
  have hs2 : Subsingleton (Ext ((ModuleCat.extendScalars φ).obj S.X₂)
      ((ModuleCat.extendScalars φ).obj Y) (k + 1)) := Ext.subsingleton_of_projective _ _ _
  have hs2' : Subsingleton (Ext (S.map (ModuleCat.extendScalars φ)).X₂
      ((ModuleCat.extendScalars φ).obj Y) (k + 1)) := hs2
  have hδQ : Function.Surjective (δQ φ Y hS' h).hom := fun x =>
    ((exact_ext_c hS' ((ModuleCat.extendScalars φ).obj Y) h) x).1 (hs2'.elim _ _)
  have hEP : Function.Exact (precompP Y S.f k).hom (δP Y hS h).hom := exact_ext_b hS Y h
  have hEQ : Function.Exact (precompQ φ Y S.f k).hom (δQ φ Y hS' h).hom :=
    exact_ext_b hS' ((ModuleCat.extendScalars φ).obj Y) h
  have hEPe : Epi (δP Y hS h) := (ModuleCat.epi_iff_surjective _).2 (δP_surj Y hS hF k h)
  have hrow1 := exact_ex φ (precompP Y S.f k) (δP Y hS h) hEP
  have hc₁ := e_natural φ Y S.f k hΨK heK heF
  have hc₂ := e_delta φ Y hS hS' h hΨM heK heM
  exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    ((ModuleCat.extendScalars φ).map (precompP Y S.f k)).hom
    ((ModuleCat.extendScalars φ).map (δP Y hS h)).hom
    (precompQ φ Y S.f k).hom (δQ φ Y hS' h).hom eF.hom eK.hom eM.hom
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, hc₁])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, hc₂]) hrow1 hEQ hsF hbK
    ((ModuleCat.epi_iff_surjective _).1 inferInstance) hδQ

/-- Tensor-side exactness in degree zero. -/
private lemma zero_P_side (C : ModuleCat.{u} P → Prop) (hC : GoodClass φ C) (Y : ModuleCat.{u} P)
    {S : ShortComplex (ModuleCat.{u} P)} (hS : S.ShortExact) (hF : Projective S.X₂)
    (hCB : C (ModuleCat.of P (LinearMap.range (precompP Y S.f 0).hom)))
    (hCE : C (EP Y S.X₃ 1)) :
    Function.Injective ((ModuleCat.extendScalars φ).map (precompP Y S.g 0)).hom ∧
    Function.Exact ((ModuleCat.extendScalars φ).map (precompP Y S.g 0)).hom
      ((ModuleCat.extendScalars φ).map (precompP Y S.f 0)).hom := by
  set ρ := precompP Y S.f 0 with hρdef
  set π := precompP Y S.g 0 with hπdef
  let B : ModuleCat.{u} P := ModuleCat.of P (LinearMap.range ρ.hom)
  let ρ' : EP Y S.X₂ 0 ⟶ B := ModuleCat.ofHom ρ.hom.rangeRestrict
  let j : B ⟶ EP Y S.X₁ 0 := ModuleCat.ofHom (LinearMap.range ρ.hom).subtype
  have hρ : ρ' ≫ j = ρ := by ext x; rfl
  have : Epi S.g := hS.epi_g
  have hπinj : Function.Injective π.hom := Ext.precomp_mk₀_injective_of_epi Y S.g
  have hexa : Function.Exact π.hom ρ.hom := exact_ext_a hS Y 0
  have hexa' : Function.Exact π.hom ρ'.hom := fun y =>
    ⟨fun h => (hexa y).1 (congrArg Subtype.val h), fun h => Subtype.ext ((hexa y).2 h)⟩
  have hρ'surj : Function.Surjective ρ'.hom := LinearMap.surjective_rangeRestrict _
  have hρ'epi : Epi ρ' := (ModuleCat.epi_iff_surjective _).2 hρ'surj
  have hw : π ≫ ρ' = 0 := ModuleCat.hom_ext (LinearMap.ext fun x => hexa'.apply_apply_eq_zero x)
  have hA : (ShortComplex.mk π ρ' hw).ShortExact := by
    have : Mono π := (ModuleCat.mono_iff_injective _).2 hπinj
    exact ShortComplex.ShortExact.mk'
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hexa') inferInstance
      inferInstance
  have hexb : Function.Exact ρ.hom (δP Y hS (add_comm 1 0)).hom := exact_ext_b hS Y (add_comm 1 0)
  have hexb' : Function.Exact j.hom (δP Y hS (add_comm 1 0)).hom := by
    intro y
    rw [hexb y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨_, x, rfl⟩, rfl⟩
    · rintro ⟨⟨_, x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  have hw2 : j ≫ δP Y hS (add_comm 1 0) = 0 :=
    ModuleCat.hom_ext (LinearMap.ext fun x => hexb'.apply_apply_eq_zero x)
  have hB : (ShortComplex.mk j (δP Y hS (add_comm 1 0)) hw2).ShortExact := by
    have : Mono j := (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype _)
    have : Epi (δP Y hS (add_comm 1 0)) := (ModuleCat.epi_iff_surjective _).2 (δP_surj Y hS hF 0 _)
    exact ShortComplex.ShortExact.mk'
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hexb') inferInstance
      inferInstance
  have hCB' : C B := hCB
  have hmonoπ : Mono ((ModuleCat.extendScalars φ).map π) :=
    hC.mono (ShortComplex.mk π ρ' hw) hA hCB'
  have hmonoj : Mono ((ModuleCat.extendScalars φ).map j) :=
    hC.mono (ShortComplex.mk j (δP Y hS (add_comm 1 0)) hw2) hB hCE
  have hexA : Function.Exact ((ModuleCat.extendScalars φ).map π).hom
      ((ModuleCat.extendScalars φ).map ρ').hom :=
    exact_ex φ π ρ' hexa'
  have hinjj : Function.Injective ((ModuleCat.extendScalars φ).map j).hom :=
    (ModuleCat.mono_iff_injective _).1 hmonoj
  have hexP : Function.Exact ((ModuleCat.extendScalars φ).map π).hom
      ((ModuleCat.extendScalars φ).map ρ).hom := by
    intro y
    have : ((ModuleCat.extendScalars φ).map ρ).hom y =
        ((ModuleCat.extendScalars φ).map j).hom (((ModuleCat.extendScalars φ).map ρ').hom y) := by
      rw [← hρ, Functor.map_comp]; rfl
    rw [this, ← map_zero ((ModuleCat.extendScalars φ).map j).hom, hinjj.eq_iff]
    exact hexA y
  exact ⟨(ModuleCat.mono_iff_injective _).1 hmonoπ, hexP⟩

/-- The degree zero step. -/
private lemma step_zero (C : ModuleCat.{u} P → Prop) (hC : GoodClass φ C) (Y : ModuleCat.{u} P)
    {S : ShortComplex (ModuleCat.{u} P)} (hS : S.ShortExact)
    (hS' : (S.map (ModuleCat.extendScalars φ)).ShortExact) (hF : Projective S.X₂)
    (hΨK : Function.Injective (Ψ φ S.X₁ ((ModuleCat.extendScalars φ).obj Y) 0))
    {eF : (ModuleCat.extendScalars φ).obj (EP Y S.X₂ 0) ⟶ EQ φ Y S.X₂ 0}
    (heF : IsE φ Y S.X₂ 0 eF) (hbF : Function.Bijective eF.hom)
    {eK : (ModuleCat.extendScalars φ).obj (EP Y S.X₁ 0) ⟶ EQ φ Y S.X₁ 0}
    (heK : IsE φ Y S.X₁ 0 eK) (hiK : Function.Injective eK.hom)
    (hCB : C (ModuleCat.of P (LinearMap.range (precompP Y S.f 0).hom)))
    (hCE : C (EP Y S.X₃ 1))
    {eM : (ModuleCat.extendScalars φ).obj (EP Y S.X₃ 0) ⟶ EQ φ Y S.X₃ 0}
    (heM : IsE φ Y S.X₃ 0 eM) : Function.Bijective eM.hom := by
  have : Projective ((ModuleCat.extendScalars φ).obj S.X₂) := projective_ex φ _
  obtain ⟨hmonoπ, hexP⟩ := zero_P_side φ C hC Y hS hF hCB hCE
  have hexQ : Function.Exact (precompQ φ Y S.g 0).hom (precompQ φ Y S.f 0).hom :=
    exact_ext_a hS' ((ModuleCat.extendScalars φ).obj Y) 0
  have hEpiQ : Epi ((ModuleCat.extendScalars φ).map S.g) := hS'.epi_g
  have hinjQ : Function.Injective (precompQ φ Y S.g 0).hom :=
    Ext.precomp_mk₀_injective_of_epi ((ModuleCat.extendScalars φ).obj Y)
      ((ModuleCat.extendScalars φ).map S.g)
  have hΨF : Function.Injective (Ψ φ S.X₂ ((ModuleCat.extendScalars φ).obj Y) 0) :=
    (Ψ_proj_bijective φ S.X₂ _ 0).1
  have hc₁ := e_natural φ Y S.g 0 hΨF heF heM
  have hc₂ := e_natural φ Y S.f 0 hΨK heK heF
  exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
    ((ModuleCat.extendScalars φ).map (precompP Y S.g 0)).hom
        ((ModuleCat.extendScalars φ).map (precompP Y S.f 0)).hom
    (precompQ φ Y S.g 0).hom (precompQ φ Y S.f 0).hom eM.hom eF.hom eK.hom
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, hc₁])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, hc₂]) hexP hexQ hbF hiK
    hmonoπ hinjQ

end ExtAdjunction

section ResolutionChain

variable {P Q : Type u} [CommRing P] [CommRing Q] (φ : P →+* Q)

/-- The degree zero comparison is bijective. -/
private def E0Good (Y F : ModuleCat.{u} P) : Prop :=
  ∀ e : (ModuleCat.extendScalars φ).obj (EP Y F 0) ⟶ EQ φ Y F 0,
    IsE φ Y F 0 e → Function.Bijective e.hom

/-- A resolution chain of length `n` along which the comparison maps are well behaved. -/
private def Chain (C : ModuleCat.{u} P → Prop) (Y : ModuleCat.{u} P) : ℕ → ModuleCat.{u} P → Prop
  | 0, M => Projective M ∧ E0Good φ Y M
  | n + 1, M => ∃ S : ShortComplex (ModuleCat.{u} P), S.ShortExact ∧ S.X₃ = M ∧
      Projective S.X₂ ∧ E0Good φ Y S.X₂ ∧ C S.X₃ ∧
      C (ModuleCat.of P (LinearMap.range (precompP Y S.f 0).hom)) ∧ C (EP Y S.X₃ 1) ∧
      Chain C Y n S.X₁

private lemma subsingleton_ex_obj (X : ModuleCat.{u} P) [Subsingleton X] :
    Subsingleton ((ModuleCat.extendScalars φ).obj X) := by
  have h : IsZero X := ModuleCat.isZero_of_subsingleton X
  have h2 : IsZero ((ModuleCat.extendScalars φ).obj X) := Functor.map_isZero _ h
  exact (ModuleCat.isZero_iff_subsingleton).1 h2

private theorem chain_bij {C : ModuleCat.{u} P → Prop} (hC : GoodClass φ C) (Y : ModuleCat.{u} P)
    (n : ℕ) :
    ∀ M : ModuleCat.{u} P, Chain φ C Y n M →
      (∀ i, Function.Bijective (Ψ φ M ((ModuleCat.extendScalars φ).obj Y) i)) ∧
      ∀ i (e : (ModuleCat.extendScalars φ).obj (EP Y M i) ⟶ EQ φ Y M i), IsE φ Y M i e →
        Function.Bijective e.hom := by
  induction n with
  | zero =>
    rintro M ⟨hM, hE0⟩
    have : Projective ((ModuleCat.extendScalars φ).obj M) := projective_ex φ M
    refine ⟨fun i => Ψ_proj_bijective φ M _ i, ?_⟩
    intro i e he
    cases i with
    | zero => exact hE0 e he
    | succ k =>
      have h1 : Subsingleton (Ext M Y (k + 1)) := Ext.subsingleton_of_projective _ _ _
      have h2 : Subsingleton (Ext ((ModuleCat.extendScalars φ).obj M)
        ((ModuleCat.extendScalars φ).obj Y) (k + 1)) := Ext.subsingleton_of_projective _ _ _
      have h3 : Subsingleton ((ModuleCat.extendScalars φ).obj (EP Y M (k + 1))) :=
        subsingleton_ex_obj φ _
      exact Function.bijective_of_subsingleton' _
  | succ n ih =>
    rintro M ⟨S, hS, rfl, hF, hE0F, hCM, hCB, hCE, hch⟩
    have hmono := hC.mono S hS hCM
    have hS' := shortExact_map_ex φ hS hmono
    obtain ⟨hΨK, hK⟩ := ih S.X₁ hch
    have hΨM := fun i => Ψ_bijective φ hC ((ModuleCat.extendScalars φ).obj Y) i S.X₃ hCM
    have : Projective ((ModuleCat.extendScalars φ).obj S.X₂) := projective_ex φ _
    have hΨF := fun i => Ψ_proj_bijective φ S.X₂ ((ModuleCat.extendScalars φ).obj Y) i
    refine ⟨hΨM, ?_⟩
    intro i e he
    cases i with
    | zero =>
      exact step_zero φ C hC Y hS hS' hF (hΨK 0).1
        (eMap_isE φ Y S.X₂ 0 (hΨF 0)) (hE0F _ (eMap_isE φ Y S.X₂ 0 (hΨF 0)))
        (eMap_isE φ Y S.X₁ 0 (hΨK 0)) (hK 0 _ (eMap_isE φ Y S.X₁ 0 (hΨK 0))).1 hCB hCE he
    | succ k =>
      have hsF : Function.Surjective (eMap φ Y S.X₂ k (hΨF k)).hom := by
        cases k with
        | zero => exact (hE0F _ (eMap_isE φ Y S.X₂ 0 (hΨF 0))).2
        | succ k' =>
          have h2 : Subsingleton (Ext ((ModuleCat.extendScalars φ).obj S.X₂)
            ((ModuleCat.extendScalars φ).obj Y) (k' + 1)) := Ext.subsingleton_of_projective _ _ _
          exact fun y => ⟨0, Subsingleton.elim _ _⟩
      exact step_succ φ Y hS hS' hF k (hΨK k).1 (hΨM (k + 1)).1
        (eMap_isE φ Y S.X₂ k (hΨF k)) hsF
        (eMap_isE φ Y S.X₁ k (hΨK k)) (hK k _ (eMap_isE φ Y S.X₁ k (hΨK k))) he

end ResolutionChain

section DegreeZero

variable {P Q : Type u} [CommRing P] [CommRing Q] (φ : P →+* Q)

private lemma evalOne_bijective (N : ModuleCat.{u} P) :
    Function.Bijective (fun h : (ModuleCat.of P P ⟶ N) => h.hom (1 : P)) := by
  constructor
  · intro h₁ h₂ h
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact h
  · intro n
    exact ⟨ModuleCat.ofHom (LinearMap.toSpanSingleton P N n), by simp⟩

/-- Evaluation at `1`, linear. -/
private noncomputable def evalOneLin (N : ModuleCat.{u} P) : (ModuleCat.of P P ⟶ N) →ₗ[P] N where
  toFun h := h.hom (1 : P)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private lemma evalOneLin_apply (N : ModuleCat.{u} P) (h : ModuleCat.of P P ⟶ N) :
    evalOneLin N h = h.hom (1 : P) := rfl

/-- `Ext^0(P, Y) → Y`. -/
private noncomputable def aLin (Y : ModuleCat.{u} P) : Ext (ModuleCat.of P P) Y 0 →ₗ[P] Y :=
  (evalOneLin Y).comp (Ext.linearEquiv₀ (R := P)).toLinearMap

private lemma aLin_bijective (Y : ModuleCat.{u} P) : Function.Bijective (aLin Y) := by
  have h1 : Function.Bijective (evalOneLin Y) := evalOne_bijective Y
  exact h1.comp (Ext.linearEquiv₀ (R := P)).bijective

private lemma linearEquiv₀_mk₀ {X Y : ModuleCat.{u} P} (h : X ⟶ Y) :
    Ext.linearEquiv₀ (R := P) (Ext.mk₀ h) = h := by
  apply (Ext.mk₀_bijective X Y).1
  rw [Ext.mk₀_linearEquiv₀_apply]

private lemma aLin_mk₀ (Y : ModuleCat.{u} P) (h : ModuleCat.of P P ⟶ Y) :
    aLin Y (Ext.mk₀ h) = h.hom (1 : P) := by
  simp [aLin, evalOneLin_apply, linearEquiv₀_mk₀]

/-- Evaluation at the unit of `1`, linear over `Q`. -/
private noncomputable def evalUnitLin (Y : ModuleCat.{u} P) :
    ((ModuleCat.extendScalars φ).obj (ModuleCat.of P P) ⟶ (ModuleCat.extendScalars φ).obj Y) →ₗ[Q]
      (ModuleCat.extendScalars φ).obj Y where
  toFun g := g.hom (unitE φ (ModuleCat.of P P) 1)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private lemma evalUnitLin_apply (Y : ModuleCat.{u} P)
    (g : (ModuleCat.extendScalars φ).obj (ModuleCat.of P P) ⟶ (ModuleCat.extendScalars φ).obj Y) :
    evalUnitLin φ Y g = g.hom (unitE φ (ModuleCat.of P P) 1) := rfl

private lemma evalUnitLin_bijective (Y : ModuleCat.{u} P) :
    Function.Bijective (evalUnitLin φ Y) :=
  (evalOne_bijective ((ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj Y))).comp
    (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv (ModuleCat.of P P)
      ((ModuleCat.extendScalars φ).obj Y)).bijective)

/-- `Ext^0_Q(φ^*P, φ^*Y) → φ^*Y`. -/
private noncomputable def bLin (Y : ModuleCat.{u} P) :
    Ext ((ModuleCat.extendScalars φ).obj (ModuleCat.of P P)) ((ModuleCat.extendScalars φ).obj Y) 0
      →ₗ[Q] (ModuleCat.extendScalars φ).obj Y :=
  (evalUnitLin φ Y).comp (Ext.linearEquiv₀ (R := Q)).toLinearMap

private lemma bLin_bijective (Y : ModuleCat.{u} P) : Function.Bijective (bLin φ Y) :=
  (evalUnitLin_bijective φ Y).comp (Ext.linearEquiv₀ (R := Q)).bijective

private lemma bLin_Ψ (Y : ModuleCat.{u} P)
    (y : Ext ((ModuleCat.extendScalars φ).obj (ModuleCat.of P P))
        ((ModuleCat.extendScalars φ).obj Y) 0)
    (h : ModuleCat.of P P ⟶ (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj Y))
    (hy : Ψ φ (ModuleCat.of P P) ((ModuleCat.extendScalars φ).obj Y) 0 y = Ext.mk₀ h) :
    bLin φ Y y = h.hom (1 : P) := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  rw [Ψ_mk₀] at hy
  have := (Ext.mk₀_bijective _ _).1 hy
  subst this
  simp only [bLin, LinearMap.comp_apply, LinearEquiv.coe_coe, linearEquiv₀_mk₀, evalUnitLin_apply,
    Adjunction.homEquiv_unit]
  rfl

private lemma E0Good_P (Y : ModuleCat.{u} P) : E0Good φ Y (ModuleCat.of P P) := by
  intro e he
  let aMor : EP Y (ModuleCat.of P P) 0 ⟶ Y := ModuleCat.ofHom (aLin Y)
  let bMor : EQ φ Y (ModuleCat.of P P) 0 ⟶ (ModuleCat.extendScalars φ).obj Y :=
    ConcreteCategory.ofHom (C := ModuleCat Q) (bLin φ Y)
  have hcomm : e ≫ bMor = (ModuleCat.extendScalars φ).map aMor := by
    apply hom_ext_unit φ
    intro x
    obtain ⟨hx, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    have h1 := he (Ext.mk₀ hx)
    rw [Θ_apply, Ext.mk₀_comp_mk₀] at h1
    have h2 := bLin_Ψ φ Y _ _ h1
    change bLin φ Y (e.hom (unitE φ (EP Y (ModuleCat.of P P) 0) (Ext.mk₀ hx))) =
      ((ModuleCat.extendScalars φ).map aMor).hom (unitE φ (EP Y (ModuleCat.of P P) 0) (Ext.mk₀ hx))
    rw [h2, extendScalars_map_unitE]
    have h5 : aMor.hom (Ext.mk₀ hx) = hx.hom (1 : P) := aLin_mk₀ Y hx
    rw [h5]
    rfl
  have hb : Function.Bijective bMor.hom := bLin_bijective φ Y
  have hab : Function.Bijective ((ModuleCat.extendScalars φ).map aMor).hom := by
    have : IsIso aMor := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact aLin_bijective Y
    exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hcomp : Function.Bijective (bMor.hom ∘ e.hom) := by
    have h3 := congrArg ModuleCat.Hom.hom hcomm
    rw [ModuleCat.hom_comp] at h3
    have h4 : (⇑bMor.hom ∘ ⇑e.hom) = ⇑((ModuleCat.extendScalars φ).map aMor).hom :=
      congrArg DFunLike.coe h3
    rw [h4]
    exact hab
  exact (Function.Bijective.of_comp_iff' hb _).1 hcomp

private lemma precompP_comp_precompP (Y : ModuleCat.{u} P) {M M₁ : ModuleCat.{u} P} (r : M ⟶ M₁)
    (s : M₁ ⟶ M) (i : ℕ) (z : Ext M Y i) :
    (precompP Y r i).hom ((precompP Y s i).hom z) = (precompP Y (r ≫ s) i).hom z := by
  rw [precompP_apply, precompP_apply, precompP_apply, ← Ext.mk₀_comp_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add 0) (zero_add i) (by omega)).symm

private lemma precompQ_comp_precompQ (Y : ModuleCat.{u} P) {M M₁ : ModuleCat.{u} P} (r : M ⟶ M₁)
    (s : M₁ ⟶ M) (i : ℕ)
    (z : Ext ((ModuleCat.extendScalars φ).obj M) ((ModuleCat.extendScalars φ).obj Y) i) :
    (precompQ φ Y r i).hom ((precompQ φ Y s i).hom z) = (precompQ φ Y (r ≫ s) i).hom z := by
  rw [precompQ_apply, precompQ_apply, precompQ_apply, Functor.map_comp, ← Ext.mk₀_comp_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add 0) (zero_add i) (by omega)).symm

private lemma precompP_add (Y : ModuleCat.{u} P) {M M' : ModuleCat.{u} P} (g h : M ⟶ M') (i : ℕ)
    (z : Ext M' Y i) :
    (precompP Y (g + h) i).hom z = (precompP Y g i).hom z + (precompP Y h i).hom z := by
  rw [precompP_apply, precompP_apply, precompP_apply, Ext.mk₀_add, Ext.add_comp]

private lemma precompQ_add (Y : ModuleCat.{u} P) {M M' : ModuleCat.{u} P} (g h : M ⟶ M') (i : ℕ)
    (z : Ext ((ModuleCat.extendScalars φ).obj M') ((ModuleCat.extendScalars φ).obj Y) i) :
    (precompQ φ Y (g + h) i).hom z = (precompQ φ Y g i).hom z + (precompQ φ Y h i).hom z := by
  rw [precompQ_apply, precompQ_apply, precompQ_apply, Functor.map_add, Ext.mk₀_add, Ext.add_comp]

private lemma precompP_id (Y : ModuleCat.{u} P) (M : ModuleCat.{u} P) (i : ℕ) (z : Ext M Y i) :
    (precompP Y (𝟙 M) i).hom z = z := by
  rw [precompP_apply, Ext.mk₀_id_comp]

private lemma precompQ_id (Y : ModuleCat.{u} P) (M : ModuleCat.{u} P) (i : ℕ)
    (z : Ext ((ModuleCat.extendScalars φ).obj M) ((ModuleCat.extendScalars φ).obj Y) i) :
    (precompQ φ Y (𝟙 M) i).hom z = z := by
  rw [precompQ_apply, CategoryTheory.Functor.map_id, Ext.mk₀_id_comp]

/-- Existence of a comparison map in degree zero. -/
private lemma exists_isE_zero (Y M : ModuleCat.{u} P) :
    ∃ e : (ModuleCat.extendScalars φ).obj (EP Y M 0) ⟶ EQ φ Y M 0, IsE φ Y M 0 e :=
  ⟨eMap φ Y M 0 (Ψ_zero_bijective φ M _), eMap_isE φ Y M 0 _⟩

private lemma E0Good_of_decomp (Y : ModuleCat.{u} P) {M M₁ M₂ : ModuleCat.{u} P}
    (s₁ : M₁ ⟶ M) (r₁ : M ⟶ M₁) (s₂ : M₂ ⟶ M) (r₂ : M ⟶ M₂)
    (h : r₁ ≫ s₁ + r₂ ≫ s₂ = 𝟙 M)
    (H₁ : E0Good φ Y M₁) (H₂ : E0Good φ Y M₂) : E0Good φ Y M := by
  intro e he
  obtain ⟨e₁, he₁⟩ := exists_isE_zero φ Y M₁
  obtain ⟨e₂, he₂⟩ := exists_isE_zero φ Y M₂
  have hb₁ := H₁ e₁ he₁
  have hb₂ := H₂ e₂ he₂
  have hΨM := (Ψ_zero_bijective φ M ((ModuleCat.extendScalars φ).obj Y)).1
  have hΨ₁ := (Ψ_zero_bijective φ M₁ ((ModuleCat.extendScalars φ).obj Y)).1
  have hΨ₂ := (Ψ_zero_bijective φ M₂ ((ModuleCat.extendScalars φ).obj Y)).1
  -- naturality squares
  have Ns₁ := e_natural φ Y s₁ 0 hΨ₁ he₁ he
  have Ns₂ := e_natural φ Y s₂ 0 hΨ₂ he₂ he
  have Nr₁ := e_natural φ Y r₁ 0 hΨM he he₁
  have Nr₂ := e_natural φ Y r₂ 0 hΨM he he₂
  -- decomposition of the identity, `P`-side
  have idP : ∀ z : Ext M Y 0,
      (precompP Y r₁ 0).hom ((precompP Y s₁ 0).hom z) +
        (precompP Y r₂ 0).hom ((precompP Y s₂ 0).hom z) = z := by
    intro z
    rw [precompP_comp_precompP, precompP_comp_precompP, ← precompP_add, h, precompP_id]
  have idQ : ∀ z : Ext ((ModuleCat.extendScalars φ).obj M) ((ModuleCat.extendScalars φ).obj Y) 0,
      (precompQ φ Y r₁ 0).hom ((precompQ φ Y s₁ 0).hom z) +
        (precompQ φ Y r₂ 0).hom ((precompQ φ Y s₂ 0).hom z) = z := by
    intro z
    rw [precompQ_comp_precompQ, precompQ_comp_precompQ, ← precompQ_add, h, precompQ_id]
  have idP' : ∀ ξ : (ModuleCat.extendScalars φ).obj (EP Y M 0),
      ((ModuleCat.extendScalars φ).map (precompP Y r₁ 0)).hom
          (((ModuleCat.extendScalars φ).map (precompP Y s₁ 0)).hom ξ) +
        ((ModuleCat.extendScalars φ).map (precompP Y r₂ 0)).hom
          (((ModuleCat.extendScalars φ).map (precompP Y s₂ 0)).hom ξ) = ξ := by
    have hid : (precompP Y s₁ 0 ≫ precompP Y r₁ 0) + (precompP Y s₂ 0 ≫ precompP Y r₂ 0) =
        𝟙 (EP Y M 0) :=
      ModuleCat.hom_ext (LinearMap.ext fun z => idP z)
    have : (ModuleCat.extendScalars φ).Additive :=
      (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
    have h2 := congrArg (fun g => ((ModuleCat.extendScalars φ).map g).hom) hid
    intro ξ
    have h3 := congrArg (fun g => g ξ) h2
    rw [Functor.map_add, Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.map_id] at h3
    exact h3
  have Ns₁' : ∀ ξ, e₁.hom (((ModuleCat.extendScalars φ).map (precompP Y s₁ 0)).hom ξ) =
      (precompQ φ Y s₁ 0).hom (e.hom ξ) := fun ξ => congrArg (fun k => k.hom ξ) Ns₁
  have Ns₂' : ∀ ξ, e₂.hom (((ModuleCat.extendScalars φ).map (precompP Y s₂ 0)).hom ξ) =
      (precompQ φ Y s₂ 0).hom (e.hom ξ) := fun ξ => congrArg (fun k => k.hom ξ) Ns₂
  have Nr₁' : ∀ t, e.hom (((ModuleCat.extendScalars φ).map (precompP Y r₁ 0)).hom t) =
      (precompQ φ Y r₁ 0).hom (e₁.hom t) := fun t => congrArg (fun k => k.hom t) Nr₁
  have Nr₂' : ∀ t, e.hom (((ModuleCat.extendScalars φ).map (precompP Y r₂ 0)).hom t) =
      (precompQ φ Y r₂ 0).hom (e₂.hom t) := fun t => congrArg (fun k => k.hom t) Nr₂
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ξ hξ
    have z₁ : ((ModuleCat.extendScalars φ).map (precompP Y s₁ 0)).hom ξ = 0 := by
      apply hb₁.1
      rw [Ns₁', hξ, map_zero, map_zero]
    have z₂ : ((ModuleCat.extendScalars φ).map (precompP Y s₂ 0)).hom ξ = 0 := by
      apply hb₂.1
      rw [Ns₂', hξ, map_zero, map_zero]
    rw [← idP' ξ, z₁, z₂, map_zero, map_zero, add_zero]
  · intro y
    obtain ⟨t₁, ht₁⟩ := hb₁.2 ((precompQ φ Y s₁ 0).hom y)
    obtain ⟨t₂, ht₂⟩ := hb₂.2 ((precompQ φ Y s₂ 0).hom y)
    refine ⟨((ModuleCat.extendScalars φ).map (precompP Y r₁ 0)).hom t₁ +
      ((ModuleCat.extendScalars φ).map (precompP Y r₂ 0)).hom t₂, ?_⟩
    rw [map_add, Nr₁', Nr₂', ht₁, ht₂]
    exact idQ y

private lemma E0Good_of_retract (Y : ModuleCat.{u} P) {M F : ModuleCat.{u} P} (s : M ⟶ F)
    (r : F ⟶ M)
    (h : s ≫ r = 𝟙 M) (HF : E0Good φ Y F) : E0Good φ Y M := by
  intro e he
  obtain ⟨eF, heF⟩ := exists_isE_zero φ Y F
  have hbF := HF eF heF
  have hΨM := (Ψ_zero_bijective φ M ((ModuleCat.extendScalars φ).obj Y)).1
  have hΨF := (Ψ_zero_bijective φ F ((ModuleCat.extendScalars φ).obj Y)).1
  have Ns := e_natural φ Y s 0 hΨM he heF
  have Nr := e_natural φ Y r 0 hΨF heF he
  have Ns' : ∀ t, e.hom (((ModuleCat.extendScalars φ).map (precompP Y s 0)).hom t) =
      (precompQ φ Y s 0).hom (eF.hom t) := fun t => congrArg (fun k => k.hom t) Ns
  have Nr' : ∀ ξ, eF.hom (((ModuleCat.extendScalars φ).map (precompP Y r 0)).hom ξ) =
      (precompQ φ Y r 0).hom (e.hom ξ) := fun ξ => congrArg (fun k => k.hom ξ) Nr
  have idP : ∀ z : Ext M Y 0, (precompP Y s 0).hom ((precompP Y r 0).hom z) = z := by
    intro z
    rw [precompP_comp_precompP, h, precompP_id]
  have idQ : ∀ z : Ext ((ModuleCat.extendScalars φ).obj M) ((ModuleCat.extendScalars φ).obj Y) 0,
      (precompQ φ Y s 0).hom ((precompQ φ Y r 0).hom z) = z := by
    intro z
    rw [precompQ_comp_precompQ, h, precompQ_id]
  have idP' : ∀ ξ : (ModuleCat.extendScalars φ).obj (EP Y M 0),
      ((ModuleCat.extendScalars φ).map (precompP Y s 0)).hom
        (((ModuleCat.extendScalars φ).map (precompP Y r 0)).hom ξ) = ξ := by
    have : precompP Y r 0 ≫ precompP Y s 0 = 𝟙 (EP Y M 0) :=
      ModuleCat.hom_ext (LinearMap.ext fun z => idP z)
    have h2 := congrArg (fun g => ((ModuleCat.extendScalars φ).map g).hom) this
    intro ξ
    simpa [CategoryTheory.Functor.map_id] using congrArg (fun g => g ξ) h2
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ξ hξ
    have z : ((ModuleCat.extendScalars φ).map (precompP Y r 0)).hom ξ = 0 := by
      apply hbF.1
      rw [Nr', hξ, map_zero, map_zero]
    rw [← idP' ξ, z, map_zero]
  · intro y
    obtain ⟨t, ht⟩ := hbF.2 ((precompQ φ Y r 0).hom y)
    refine ⟨((ModuleCat.extendScalars φ).map (precompP Y s 0)).hom t, ?_⟩
    rw [Ns', ht]
    exact idQ y

private lemma E0Good_of_subsingleton (Y M : ModuleCat.{u} P) [Subsingleton M] : E0Good φ Y M := by
  intro e he
  have hM : IsZero M := ModuleCat.isZero_of_subsingleton M
  have hMQ : IsZero ((ModuleCat.extendScalars φ).obj M) := Functor.map_isZero _ hM
  have h1 : Subsingleton (Ext M Y 0) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective M Y).2 a
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective M Y).2 b
    rw [hM.eq_of_src f g]
  have h3 : Subsingleton ((ModuleCat.extendScalars φ).obj (EP Y M 0)) := subsingleton_ex_obj φ _
  have h2 : Subsingleton (Ext ((ModuleCat.extendScalars φ).obj M)
      ((ModuleCat.extendScalars φ).obj Y) 0) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 a
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).2 b
    rw [hMQ.eq_of_src f g]
  exact Function.bijective_of_subsingleton' _

private lemma E0Good_of_prodEquiv (Y : ModuleCat.{u} P) {X X₁ X₂ : Type u} [AddCommGroup X]
    [Module P X]
    [AddCommGroup X₁] [Module P X₁] [AddCommGroup X₂] [Module P X₂]
    (ε : X ≃ₗ[P] X₁ × X₂) (H₁ : E0Good φ Y (ModuleCat.of P X₁))
    (H₂ : E0Good φ Y (ModuleCat.of P X₂)) : E0Good φ Y (ModuleCat.of P X) := by
  refine E0Good_of_decomp φ Y (M := ModuleCat.of P X) (M₁ := ModuleCat.of P X₁)
    (M₂ := ModuleCat.of P X₂)
    (ModuleCat.ofHom (ε.symm.toLinearMap ∘ₗ LinearMap.inl P X₁ X₂))
    (ModuleCat.ofHom (LinearMap.fst P X₁ X₂ ∘ₗ ε.toLinearMap))
    (ModuleCat.ofHom (ε.symm.toLinearMap ∘ₗ LinearMap.inr P X₁ X₂))
    (ModuleCat.ofHom (LinearMap.snd P X₁ X₂ ∘ₗ ε.toLinearMap)) ?_ H₁ H₂
  ext x
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.add_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, LinearMap.inr_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, ModuleCat.hom_id, LinearMap.id_apply]
  rw [← map_add]
  simp

private lemma E0Good_pi (Y : ModuleCat.{u} P) (n : ℕ) : E0Good φ Y
    (ModuleCat.of P (Fin n → P)) := by
  induction n with
  | zero =>
    have : Subsingleton (ModuleCat.of P (Fin 0 → P)) := inferInstanceAs (Subsingleton (Fin 0 → P))
    exact E0Good_of_subsingleton φ Y _
  | succ n ih =>
    exact E0Good_of_prodEquiv φ Y
      (LinearEquiv.piCongrLeft P (fun _ => P) (finSuccEquiv n) ≪≫ₗ LinearEquiv.piOptionEquivProd P)
      (E0Good_P φ Y) ih

private lemma E0Good_of_finite_projective (Y : ModuleCat.{u} P) (X : Type u) [AddCommGroup X]
    [Module P X]
    [Module.Finite P X] [Module.Projective P X] : E0Good φ Y (ModuleCat.of P X) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective P X
  refine E0Good_of_retract φ Y (ModuleCat.ofHom g) (ModuleCat.ofHom f) ?_ (E0Good_pi φ Y n)
  ext x
  exact LinearMap.congr_fun hfg x

end DegreeZero

section Retraction

private lemma exists_retraction {S A B C : Type*} [CommRing S] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module S A] [Module S B] [Module S C] (i : A →ₗ[S] B) (p : B →ₗ[S] C)
    (hi : Function.Injective i) (hex : Function.Exact i p) [Module.Projective S C]
    (hp : Function.Surjective p) : ∃ ρ : B →ₗ[S] A, ρ ∘ₗ i = LinearMap.id := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property p LinearMap.id hp
  let r := (hex.splitInjectiveEquiv hp).symm (hex.splitSurjectiveEquiv hi ⟨σ, hσ⟩)
  exact ⟨r.1, r.2⟩

/-- A short exact sequence `0 → X → Y → Z → 0` of `R`-modules whose cokernel becomes projective
over `R_g` splits after base change to `R_g`. -/
private lemma exists_retraction_baseChange {R : Type u} [CommRing R] (g : R) {X Y Z : Type u}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z]
    (i : X →ₗ[R] Y) (p : Y →ₗ[R] Z) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p)
    [Module.Projective (Localization.Away g) (Localization.Away g ⊗[R] Z)] :
    ∃ ρ : Localization.Away g ⊗[R] Y →ₗ[Localization.Away g] Localization.Away g ⊗[R] X,
      ρ ∘ₗ i.baseChange (Localization.Away g) = LinearMap.id := by
  let Rg := Localization.Away g
  haveI : Module.Flat R Rg := IsLocalization.flat Rg (Submonoid.powers g)
  let i' : Rg ⊗[R] X →ₗ[Rg] Rg ⊗[R] Y := i.baseChange Rg
  let p' : Rg ⊗[R] Y →ₗ[Rg] Rg ⊗[R] Z := p.baseChange Rg
  have hi' : Function.Injective i' := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := Rg) i hi
    simpa [i', LinearMap.baseChange_eq_ltensor] using this
  have hp' : Function.Surjective p' := by
    simpa [p', LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective Rg hp
  have hex' : Function.Exact i' p' := by
    simpa [i', p', LinearMap.baseChange_eq_ltensor] using lTensor_exact Rg hex hp
  exact exists_retraction i' p' hi' hex' hp'

private lemma kappa_inj {R κ : Type u} [CommRing R] [CommRing κ] [Algebra R κ] (g : R)
    (hg : IsUnit (algebraMap R κ g)) {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z] (i : X →ₗ[R] Y) (p : Y →ₗ[R] Z)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    [Module.Projective (Localization.Away g) (Localization.Away g ⊗[R] Z)] :
    Function.Injective (LinearMap.lTensor κ i) := by
  let Rg := Localization.Away g
  letI : Algebra Rg κ := (IsLocalization.Away.lift g hg).toAlgebra
  haveI : IsScalarTower R Rg κ := IsScalarTower.of_algebraMap_eq' (by
    ext r
    simp [RingHom.algebraMap_toAlgebra])
  obtain ⟨ρ, hρ⟩ := exists_retraction_baseChange g i p hi hp hex
  have key : ∀ t : κ ⊗[R] X, LinearMap.lTensor κ i t =
      TensorProduct.AlgebraTensorModule.cancelBaseChange R Rg Rg κ Y
        (LinearMap.lTensor κ (i.baseChange Rg)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange R Rg Rg κ X).symm t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => simp
    | add a b ha hb => simp [map_add, ha, hb]
  have hinj' : Function.Injective (LinearMap.lTensor κ (i.baseChange Rg)) := by
    have hl : Function.LeftInverse (LinearMap.lTensor κ ρ)
        (LinearMap.lTensor κ (i.baseChange Rg)) := by
      intro t
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hρ, LinearMap.lTensor_id,
        LinearMap.id_apply]
    exact hl.injective
  intro a b hab
  rw [key, key] at hab
  have := (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rg Rg κ Y).injective hab
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rg Rg κ X).symm.injective
    (hinj' this)

section Pushout

variable {R P Q κ : Type u} [CommRing R] [CommRing P] [CommRing Q] [CommRing κ]
  [Algebra R P] [Algebra R κ] [Algebra P Q] [Algebra κ Q] [Algebra R Q]
  [IsScalarTower R P Q] [IsScalarTower R κ Q] [Algebra.IsPushout R κ P Q]

private lemma tensorQ_inj (g : R) (hg : IsUnit (algebraMap R κ g)) {X Y Z : Type u} [AddCommGroup X]
    [AddCommGroup Y] [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z] [Module P X]
    [Module P Y] [Module P Z] [IsScalarTower R P X] [IsScalarTower R P Y] [IsScalarTower R P Z]
    (i : X →ₗ[P] Y) (p : Y →ₗ[P] Z) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p)
    [Module.Projective (Localization.Away g) (Localization.Away g ⊗[R] Z)] :
    Function.Injective (LinearMap.lTensor Q i) := by
  have hκ := kappa_inj (κ := κ) g hg (i.restrictScalars R) (p.restrictScalars R) hi hp hex
  have key : ∀ u : κ ⊗[R] X, LinearMap.lTensor Q i
      ((Algebra.IsPushout.cancelBaseChange R κ P Q X).symm u) =
      (Algebra.IsPushout.cancelBaseChange R κ P Q Y).symm
        (LinearMap.lTensor κ (i.restrictScalars R) u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul s x => simp
    | add a b ha hb => simp [map_add, ha, hb]
  intro t₁ t₂ h
  obtain ⟨u₁, rfl⟩ := (Algebra.IsPushout.cancelBaseChange R κ P Q X).symm.surjective t₁
  obtain ⟨u₂, rfl⟩ := (Algebra.IsPushout.cancelBaseChange R κ P Q X).symm.surjective t₂
  rw [key, key] at h
  exact congrArg _ (hκ ((Algebra.IsPushout.cancelBaseChange R κ P Q Y).symm.injective h))

end Pushout

end Retraction

/-- The `R`-module structure on a `P`-module, through `algebraMap R P`. It is a local instance
for the generic freeness argument, which tensors `P`-modules with localizations of `R`. -/
@[reducible] private noncomputable def moduleOfModuleCat {R P : Type u} [CommRing R]
    [CommRing P] [Algebra R P] (M : ModuleCat.{u} P) : Module R M :=
  Module.compHom M (algebraMap R P)

attribute [local instance low] moduleOfModuleCat

private theorem isScalarTower_moduleOfModuleCat {R P : Type u} [CommRing R] [CommRing P]
    [Algebra R P] (M : ModuleCat.{u} P) : IsScalarTower R P M :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] isScalarTower_moduleOfModuleCat

section GenericFreeness

section Bridge

variable {P Q : Type u} [CommRing P] [CommRing Q] [Algebra P Q]

/-- `Q` as a `P`-module, restricted along the structure map, is the usual one. -/
private noncomputable def restrictEquiv :
    (ModuleCat.restrictScalars (algebraMap P Q)).obj (ModuleCat.of Q Q) ≃ₗ[P] Q where
  toFun q := q
  invFun q := q
  map_add' _ _ := rfl
  map_smul' a q := by
    simp only [RingHom.id_apply]
    rw [ModuleCat.restrictScalars.smul_def]
    exact (Algebra.smul_def a (show Q from q)).symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- the identification of the carrier of `ex M` with `Q ⊗[P] M` -/
private noncomputable def exEquiv (M : ModuleCat.{u} P) :
    (ModuleCat.extendScalars (algebraMap P Q)).obj M ≃+ Q ⊗[P] M :=
  (TensorProduct.congr (restrictEquiv (P := P) (Q := Q)) (LinearEquiv.refl P M)).toAddEquiv

private lemma exEquiv_map {M N : ModuleCat.{u} P} (f : M ⟶ N)
    (t : (ModuleCat.extendScalars (algebraMap P Q)).obj M) :
    exEquiv N (((ModuleCat.extendScalars (algebraMap P Q)).map f).hom t) =
      LinearMap.lTensor Q f.hom (exEquiv M t) := by
  refine TensorProduct.induction_on (motive := fun t : TensorProduct P
    ((ModuleCat.restrictScalars (algebraMap P Q)).obj (ModuleCat.of Q Q)) M =>
      exEquiv N (((ModuleCat.extendScalars (algebraMap P Q)).map f).hom t) =
        LinearMap.lTensor Q f.hom (exEquiv M t)) t ?_ ?_ ?_
  · show exEquiv N (((ModuleCat.extendScalars (algebraMap P Q)).map f).hom
      (0 : (ModuleCat.extendScalars (algebraMap P Q)).obj M)) =
        LinearMap.lTensor Q f.hom (exEquiv M (0 : (ModuleCat.extendScalars (algebraMap P Q)).obj M))
    rw [map_zero, map_zero, map_zero, map_zero]
  · intro q m
    rfl
  · intro a b ha hb
    show exEquiv N (((ModuleCat.extendScalars (algebraMap P Q)).map f).hom
      ((a : (ModuleCat.extendScalars (algebraMap P Q)).obj M) +
        (b : (ModuleCat.extendScalars (algebraMap P Q)).obj M))) =
        LinearMap.lTensor Q f.hom
            (exEquiv M ((a : (ModuleCat.extendScalars (algebraMap P Q)).obj M) +
        (b : (ModuleCat.extendScalars (algebraMap P Q)).obj M)))
    erw [map_add, map_add, map_add, map_add]
    exact congrArg₂ _ ha hb

private lemma mono_ex_of_injective {M N : ModuleCat.{u} P} (f : M ⟶ N)
    (hf : Function.Injective (LinearMap.lTensor Q f.hom)) :
    Mono ((ModuleCat.extendScalars (algebraMap P Q)).map f) := by
  rw [ModuleCat.mono_iff_injective]
  intro a b hab
  have := congrArg (exEquiv N) hab
  rw [exEquiv_map, exEquiv_map] at this
  exact (exEquiv M).injective (hf this)

end Bridge

section Good

private lemma projective_restrict {R P X : Type u} [CommRing R] [CommRing P] [Algebra R P]
    [Module.Free R P] [AddCommGroup X] [Module P X] [Module R X] [IsScalarTower R P X]
    [Module.Projective P X] : Module.Projective R X := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective P X)
  haveI : Module.Free R (X →₀ P) := Module.Free.finsupp R P X
  have : Module.Projective R (X →₀ P) := inferInstance
  exact Module.Projective.of_split (s.restrictScalars R)
    ((Finsupp.linearCombination P id).restrictScalars R) (by ext x; exact hs x)

private lemma proj_sub_of_exact {R : Type u} [CommRing R] (h : R) {X Y Z : Type u} [AddCommGroup X]
    [AddCommGroup Y] [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z]
    (i : X →ₗ[R] Y) (p : Y →ₗ[R] Z)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    [Module.Projective (Localization.Away h) (Localization.Away h ⊗[R] Y)]
    [Module.Projective (Localization.Away h) (Localization.Away h ⊗[R] Z)] :
    Module.Projective (Localization.Away h) (Localization.Away h ⊗[R] X) := by
  obtain ⟨ρ, hρ⟩ := exists_retraction_baseChange h i p hi hp hex
  exact Module.Projective.of_split (i.baseChange _) ρ hρ

variable {R P Q κ : Type u} [CommRing R] [CommRing P] [CommRing Q] [CommRing κ]
  [Algebra R P]

/-- The class of `P`-modules that become projective over `R_h`, for some divisor `h` of `g`. -/
private def Cf (g : R) (M : ModuleCat.{u} P) : Prop :=
  ∃ h : R, h ∣ g ∧ Module.Projective (Localization.Away h) (Localization.Away h ⊗[R] M)

private lemma cf_goodClass [Module.Free R P] [Algebra R κ] [Algebra P Q] [Algebra κ Q] [Algebra R Q]
    [IsScalarTower R P Q] [IsScalarTower R κ Q] [Algebra.IsPushout R κ P Q] (g : R)
    (hg : IsUnit (algebraMap R κ g)) : GoodClass (algebraMap P Q) (Cf (R := R) g) := by
  constructor
  · intro S hS ⟨h, hdvd, hproj⟩
    have hunit : IsUnit (algebraMap R κ h) := isUnit_of_dvd_unit (map_dvd _ hdvd) hg
    haveI := hproj
    apply mono_ex_of_injective
    have hinj : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).1 hS.mono_f
    have hsurj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).1 hS.epi_g
    have hex : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    exact tensorQ_inj (κ := κ) h hunit S.f.hom S.g.hom hinj hsurj hex
  · intro S hS hF ⟨h, hdvd, hproj⟩
    refine ⟨h, hdvd, ?_⟩
    haveI := hproj
    have hinj : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).1 hS.mono_f
    have hsurj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).1 hS.epi_g
    have hex : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    haveI : Module.Projective P S.X₂ := (IsProjective.iff_projective (R := P) (S.X₂ : Type u)).2 hF
    haveI : Module.Projective R S.X₂ := projective_restrict (R := R) (P := P)
    haveI : Module.Projective (Localization.Away h) (Localization.Away h ⊗[R] S.X₂) :=
      Module.Projective.tensorProduct
    exact proj_sub_of_exact h (R := R) (X := S.X₁) (Y := S.X₂) (Z := S.X₃)
      (S.f.hom.restrictScalars R) (S.g.hom.restrictScalars R) hinj hsurj hex

end Good

end GenericFreeness

private lemma Chain.mono {P Q : Type u} [CommRing P] [CommRing Q] (φ : P →+* Q)
    {C C' : ModuleCat.{u} P → Prop} (h : ∀ M, C M → C' M) (Y : ModuleCat.{u} P) (n : ℕ) :
    ∀ M, Chain φ C Y n M → Chain φ C' Y n M := by
  induction n with
  | zero => intro M hM; exact hM
  | succ n ih =>
    rintro M ⟨S, hS, hM, hF, hE, h3, hB, hE1, hch⟩
    exact ⟨S, hS, hM, hF, hE, h _ h3, h _ hB, h _ hE1, ih _ hch⟩

section Exist

variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]

private lemma Cf_mono {g g' : R} (hg : g ∣ g') {M : ModuleCat.{u} P} (h : Cf g M) : Cf g' M := by
  obtain ⟨h', hd, hp⟩ := h
  exact ⟨h', hd.trans hg, hp⟩

private lemma finite_ext0 [IsNoetherianRing P] (M : ModuleCat.{u} P) [Module.Finite P M] :
    Module.Finite P (Ext M (ModuleCat.of P P) 0) := by
  obtain ⟨k, f₀, hf₀⟩ := Module.Finite.exists_fin' P M
  let F₀ : ModuleCat.{u} P := ModuleCat.of P (Fin k → P)
  let π : F₀ ⟶ M := ModuleCat.ofHom f₀
  have : Epi π := (ModuleCat.epi_iff_surjective _).2 hf₀
  have hinj : Function.Injective (precompP (ModuleCat.of P P) π 0).hom :=
    Ext.precomp_mk₀_injective_of_epi (ModuleCat.of P P) π
  have hF : Module.Finite P (Ext F₀ (ModuleCat.of P P) 0) := by
    have e : Ext F₀ (ModuleCat.of P P) 0 ≃ₗ[P] ((Fin k → P) →ₗ[P] P) :=
      (Ext.linearEquiv₀ (R := P)).trans ModuleCat.homLinearEquiv
    exact Module.Finite.equiv e.symm
  haveI : IsNoetherian P (Ext F₀ (ModuleCat.of P P) 0) :=
    isNoetherian_of_isNoetherianRing_of_finite P _
  exact Module.Finite.of_injective (precompP (ModuleCat.of P P) π 0).hom hinj

private theorem exists_chain [IsDomain R] [IsNoetherianRing P]
    (hgen : ∀ N : ModuleCat.{u} P, Module.Finite P N → ∃ g : R, g ≠ 0 ∧ Cf g N) :
    ∀ (n : ℕ) (M : ModuleCat.{u} P), Module.Finite P M → HasProjectiveDimensionLT M (n + 1) →
      ∃ g : R, g ≠ 0 ∧ ∀ {Q : Type u} [CommRing Q] (φ : P →+* Q),
        Chain φ (Cf g) (ModuleCat.of P P) n M := by
  intro n
  induction n with
  | zero =>
    intro M hfin hpd
    refine ⟨1, one_ne_zero, fun {Q} _ φ => ?_⟩
    have hproj : Projective M := (projective_iff_hasProjectiveDimensionLT_one (X := M)).2 hpd
    refine ⟨hproj, ?_⟩
    haveI : Module.Projective P M := (IsProjective.iff_projective (R := P) (M : Type u)).2 hproj
    exact E0Good_of_finite_projective φ _ (M : Type u)
  | succ n ih =>
    intro M hfin hpd
    obtain ⟨m, f₀, hf₀⟩ := Module.Finite.exists_fin' P M
    let F : ModuleCat.{u} P := ModuleCat.of P (Fin m → P)
    let S : ShortComplex (ModuleCat.{u} P) :=
      ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker f₀).subtype)
        (ModuleCat.ofHom f₀ : F ⟶ M) (by ext x; exact x.2)
    have hex : Function.Exact (ModuleCat.ofHom (LinearMap.ker f₀).subtype).hom
        (ModuleCat.ofHom f₀ : F ⟶ M).hom := LinearMap.exact_subtype_ker_map f₀
    have hS : S.ShortExact := by
      have : Mono S.f := (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype _)
      have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hf₀
      exact ShortComplex.ShortExact.mk'
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hex) inferInstance
        inferInstance
    have hSproj : Projective S.X₂ := inferInstanceAs (Projective (ModuleCat.of P (Fin m → P)))
    haveI : Module.Finite P S.X₁ :=
      Module.IsNoetherian.finite P (LinearMap.ker f₀)
    have hpdK : HasProjectiveDimensionLT S.X₁ (n + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff n hSproj).1 hpd
    obtain ⟨g₀, hg₀, hch⟩ := ih S.X₁ inferInstance hpdK
    haveI : Module.Finite P S.X₂ := inferInstanceAs (Module.Finite P (Fin m → P))
    haveI : Module.Finite P (EP (ModuleCat.of P P) S.X₂ 0) := finite_ext0 _
    haveI : Module.Finite P (EP (ModuleCat.of P P) S.X₁ 0) := finite_ext0 _
    obtain ⟨gM, hgM, hCM⟩ := hgen M hfin
    obtain ⟨gB, hgB, hCB⟩ := hgen
      (ModuleCat.of P (LinearMap.range (precompP (ModuleCat.of P P) S.f 0).hom))
      inferInstance
    haveI : Module.Finite P (EP (ModuleCat.of P P) S.X₃ 1) :=
      Module.Finite.of_surjective (δP (ModuleCat.of P P) hS (add_comm 1 0)).hom
        (δP_surj _ hS hSproj 0 (add_comm 1 0))
    obtain ⟨gE, hgE, hCE⟩ := hgen (EP (ModuleCat.of P P) S.X₃ 1) inferInstance
    have d₀ : g₀ ∣ g₀ * gM * gB * gE := ⟨gM * gB * gE, by ring⟩
    have dM : gM ∣ g₀ * gM * gB * gE := ⟨g₀ * gB * gE, by ring⟩
    have dB : gB ∣ g₀ * gM * gB * gE := ⟨g₀ * gM * gE, by ring⟩
    have dE : gE ∣ g₀ * gM * gB * gE := ⟨g₀ * gM * gB, by ring⟩
    refine ⟨g₀ * gM * gB * gE, mul_ne_zero (mul_ne_zero (mul_ne_zero hg₀ hgM) hgB) hgE,
      fun {Q} _ φ => ?_⟩
    refine ⟨S, hS, rfl, hSproj, E0Good_pi φ _ m, Cf_mono dM hCM, Cf_mono dB hCB,
      Cf_mono dE hCE, ?_⟩
    exact Chain.mono φ (fun N hN => Cf_mono d₀ hN) _ n _ (hch φ)

end Exist

section Gen

variable {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]

private lemma exists_cf_of_finite [IsDomain R] [Algebra.FiniteType R P] (N : ModuleCat.{u} P)
    [Module.Finite P N] : ∃ g : R, g ≠ 0 ∧ Cf g N := by
  obtain ⟨g, hg0, hF⟩ := Algebra.exists_ne_zero_isFinitePresentationFreeAway (R := R) (S := P)
    (M := N)
  refine ⟨g, hg0, g, dvd_rfl, ?_⟩
  have hfree := hF.2.2.2
  haveI : Algebra.IsPushout R (Localization.Away g) P
      (Localization (Algebra.algebraMapSubmonoid P (Submonoid.powers g))) :=
    ((Algebra.isLocalization_iff_isPushout (Submonoid.powers g) (Localization.Away g)).1
      inferInstance).symm
  let e := Algebra.IsPushout.cancelBaseChange R (Localization.Away g) P
    (Localization (Algebra.algebraMapSubmonoid P (Submonoid.powers g))) N
  haveI : Module.Free (Localization.Away g) (Localization.Away g ⊗[R] N) :=
    Module.Free.of_equiv e
  infer_instance

end Gen

/-- Along a syzygy chain of `M` whose modules are projective after inverting `g`, and for a
pushout `Q = κ ⊗_R P` with `g` a unit in `κ`, the comparison map
`Q ⊗_P Ext^i_P(M, P) → Ext^i_Q(Q ⊗_P M, Q ⊗_P P)` is a linear isomorphism. -/
private theorem exists_linearEquiv_ext_of_chain {R P Q κ : Type u} [CommRing R] [CommRing P]
    [CommRing Q] [CommRing κ] [Algebra R P] [Algebra R κ] [Algebra P Q] [Algebra κ Q] [Algebra R Q]
    [IsScalarTower R P Q] [IsScalarTower R κ Q] [Algebra.IsPushout R κ P Q] [Module.Free R P]
    (φ : P →+* Q) (hφ : φ = algebraMap P Q) (g : R) (hg : IsUnit (algebraMap R κ g))
    (M : ModuleCat.{u} P) (n : ℕ) (hch : Chain φ (Cf g) (ModuleCat.of P P) n M) (i : ℕ) :
    ∃ e : (ModuleCat.extendScalars φ).obj (ModuleCat.of P (Ext M (ModuleCat.of P P) i)) ≃ₗ[Q]
        Ext ((ModuleCat.extendScalars φ).obj M)
          ((ModuleCat.extendScalars φ).obj (ModuleCat.of P P)) i,
      ∀ x : Ext M (ModuleCat.of P P) i,
        Ψ φ M ((ModuleCat.extendScalars φ).obj (ModuleCat.of P P)) i
          (e (unitE φ (ModuleCat.of P (Ext M (ModuleCat.of P P) i)) x)) =
          Θ φ (ModuleCat.of P P) M i x := by
  subst hφ
  have hC := cf_goodClass (P := P) (Q := Q) (κ := κ) g hg
  obtain ⟨hΨ, hbij⟩ := chain_bij (algebraMap P Q) hC (ModuleCat.of P P) n M hch
  exact ⟨LinearEquiv.ofBijective (eMap (algebraMap P Q) (ModuleCat.of P P) M i (hΨ i)).hom
    (hbij i _ (eMap_isE _ _ M i (hΨ i))), fun x => eMap_isE _ _ M i (hΨ i) x⟩

/-- **Generic base change of `Ext^i_P(A, P)` to the fibres.** There is a nonzero `f : R` such
that for every prime `s ∌ f` and every `i` the canonical comparison
`κ(s)[x] ⊗_P Ext^i_P(A, P) → Ext^i_{κ(s)[x]}(κ(s)[x] ⊗_P A, κ(s)[x] ⊗_P P)` is an isomorphism.
Since `P` is regular of finite dimension, `A` has a finite chain of syzygy sequences with finite
free middle terms (`exists_chain`); generic freeness of the finitely many modules in it gives one
`f`, and along the chain the comparison maps are bijective (`exists_linearEquiv_ext_of_chain`). -/
private theorem exists_ne_zero_ext_baseChange_generic
    (k : Type u) [Field k] {R : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [IsRegularRing R]
    {σ : Type u} [Finite σ] (I : Ideal (MvPolynomial σ R)) :
    ∃ f : R, f ≠ 0 ∧
      (∀ (s : PrimeSpectrum R), f ∉ s.asIdeal → ∀ i : ℕ,
        let φ : MvPolynomial σ R →+* MvPolynomial σ s.asIdeal.ResidueField :=
          MvPolynomial.map (algebraMap R s.asIdeal.ResidueField)
        let adj := ModuleCat.extendRestrictScalarsAdj φ
        let Aₘ : ModuleCat.{u} (MvPolynomial σ R) := ModuleCat.of _ (MvPolynomial σ R ⧸ I)
        let Pₘ : ModuleCat.{u} (MvPolynomial σ R) := ModuleCat.of _ (MvPolynomial σ R)
        ∃ e : (ModuleCat.extendScalars φ).obj
            (ModuleCat.of _ (Abelian.Ext Aₘ Pₘ i)) ≃ₗ[MvPolynomial σ s.asIdeal.ResidueField]
            Abelian.Ext ((ModuleCat.extendScalars φ).obj Aₘ)
              ((ModuleCat.extendScalars φ).obj Pₘ) i,
          ∀ x : Abelian.Ext Aₘ Pₘ i,
            (Abelian.Ext.mk₀ (adj.unit.app Aₘ)).comp
                ((e (adj.unit.app (ModuleCat.of _ (Abelian.Ext Aₘ Pₘ i)) x)).mapExactFunctor
                  (ModuleCat.restrictScalars φ)) (zero_add i) =
              x.comp (Abelian.Ext.mk₀ (adj.unit.app Pₘ)) (add_zero i)) := by
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_of_finiteType k (MvPolynomial σ R)
  have hpd := hasProjectiveDimensionLT_of_ringKrullDim_eq n hn
      (ModuleCat.of _ (MvPolynomial σ R ⧸ I))
  obtain ⟨g, hg0, hch⟩ := exists_chain (R := R) (P := MvPolynomial σ R)
    (fun N _ => exists_cf_of_finite N) n (ModuleCat.of _ (MvPolynomial σ R ⧸ I)) inferInstance hpd
  refine ⟨g, hg0, fun s hs i => ?_⟩
  have hunit : IsUnit (algebraMap R s.asIdeal.ResidueField g) := by
    refine (Ne.isUnit ?_)
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact hs
  intro φ adj Aₘ Pₘ
  letI : Algebra (MvPolynomial σ R) (MvPolynomial σ s.asIdeal.ResidueField) :=
    MvPolynomial.algebraMvPolynomial
  exact exists_linearEquiv_ext_of_chain (R := R) (P := MvPolynomial σ R)
      (Q := MvPolynomial σ s.asIdeal.ResidueField)
    (κ := s.asIdeal.ResidueField) φ MvPolynomial.algebraMap_def.symm g hunit _ n (hch φ) i

/-- **Generic base change for `Ext` into a polynomial ring.** Let `R` be a regular domain of
finite type over a field, `P = R[x_σ]` with `σ` finite, and `A = P ⧸ I`. There is a nonzero
`f : R` such that `A_f` is flat over `R` and, for every prime `s` of `R` with `f ∉ s`, writing
`φ : P → κ(s)[x_σ]` for the reduction, the canonical map
`κ(s)[x_σ] ⊗_P Ext^i_P(A, P) → Ext^i_{κ(s)[x_σ]}(κ(s)[x_σ] ⊗_P A, κ(s)[x_σ] ⊗_P P)` is a linear
isomorphism, characterised by compatibility with restriction along `φ` and the units of the
extension–restriction adjunction. Moreover all these `Ext` modules vanish in degrees above some
`N`. -/
@[mmp "lem_mmp_generic_ext_base_change"]
public theorem exists_ne_zero_flat_and_ext_baseChange
    (k : Type u) [Field k] {R : Type u} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [IsRegularRing R]
    {σ : Type u} [Finite σ] (I : Ideal (MvPolynomial σ R)) :
    ∃ f : R, f ≠ 0 ∧
      Module.Flat R (Localization.Away (algebraMap R (MvPolynomial σ R ⧸ I) f)) ∧
      (∀ (s : PrimeSpectrum R), f ∉ s.asIdeal → ∀ i : ℕ,
        let φ : MvPolynomial σ R →+* MvPolynomial σ s.asIdeal.ResidueField :=
          MvPolynomial.map (algebraMap R s.asIdeal.ResidueField)
        let adj := ModuleCat.extendRestrictScalarsAdj φ
        let Aₘ : ModuleCat.{u} (MvPolynomial σ R) := ModuleCat.of _ (MvPolynomial σ R ⧸ I)
        let Pₘ : ModuleCat.{u} (MvPolynomial σ R) := ModuleCat.of _ (MvPolynomial σ R)
        ∃ e : (ModuleCat.extendScalars φ).obj
            (ModuleCat.of _ (Abelian.Ext Aₘ Pₘ i)) ≃ₗ[MvPolynomial σ s.asIdeal.ResidueField]
            Abelian.Ext ((ModuleCat.extendScalars φ).obj Aₘ)
              ((ModuleCat.extendScalars φ).obj Pₘ) i,
          ∀ x : Abelian.Ext Aₘ Pₘ i,
            (Abelian.Ext.mk₀ (adj.unit.app Aₘ)).comp
                ((e (adj.unit.app (ModuleCat.of _ (Abelian.Ext Aₘ Pₘ i)) x)).mapExactFunctor
                  (ModuleCat.restrictScalars φ)) (zero_add i) =
              x.comp (Abelian.Ext.mk₀ (adj.unit.app Pₘ)) (add_zero i)) ∧
      ∃ N : ℕ, ∀ i : ℕ, N < i →
        Subsingleton (Abelian.Ext (ModuleCat.of (MvPolynomial σ R) (MvPolynomial σ R ⧸ I))
          (ModuleCat.of (MvPolynomial σ R) (MvPolynomial σ R)) i) ∧
        ∀ s : PrimeSpectrum R, f ∉ s.asIdeal →
          let φ : MvPolynomial σ R →+* MvPolynomial σ s.asIdeal.ResidueField :=
            MvPolynomial.map (algebraMap R s.asIdeal.ResidueField)
          Subsingleton (Abelian.Ext
            ((ModuleCat.extendScalars φ).obj
              (ModuleCat.of (MvPolynomial σ R) (MvPolynomial σ R ⧸ I)))
            ((ModuleCat.extendScalars φ).obj
              (ModuleCat.of (MvPolynomial σ R) (MvPolynomial σ R))) i) := by
  obtain ⟨f, hf, he⟩ := exists_ne_zero_ext_baseChange_generic k I
  obtain ⟨g, hg, hflat⟩ :=
    exists_ne_zero_flat_localizationAway (R := R) (S := MvPolynomial σ R ⧸ I)
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_of_finiteType k (MvPolynomial σ R)
  have : Fintype σ := Fintype.ofFinite σ
  refine ⟨f * g, mul_ne_zero hf hg, ?_,
    fun s hs => he s fun h => hs (s.asIdeal.mul_mem_right g h),
    max n (Fintype.card σ), fun i hi => ⟨?_, fun s _ => ?_⟩⟩
  · rw [map_mul]
    exact flat_localizationAway_mul _ _
  · exact subsingleton_ext_of_ringKrullDim_eq n hn _ _ i (lt_of_le_of_lt (le_max_left _ _) hi)
  · refine subsingleton_ext_of_ringKrullDim_eq (Fintype.card σ) ?_ _ _ i
      (lt_of_le_of_lt (le_max_right _ _) hi)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      ENat.card_eq_coe_fintype_card]
    simp

end MMP.Foundations

namespace MMP.Mori

open CategoryTheory AlgebraicGeometry
open scoped WithZero

private theorem valuation_eq_adic_of_dominated
    {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K]
    (v : Valuation K ℤᵐ⁰) (hv : Function.Surjective v)
    (h1 : ∀ a : O, v (algebraMap O K a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal O, v (algebraMap O K a) < 1) :
    v = (IsDiscreteValuationRing.maximalIdeal O).valuation K := by
  refine MMP.Positivity.DivisorOver.valuation_eq_of_isDiscreteValuationRing h1 h2 (hv _)
    (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _) (fun a ha => ?_) ?_
  · exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 ha
  · obtain ⟨ϖ, hϖ⟩ := (IsDiscreteValuationRing.maximalIdeal O).valuation_exists_uniformizer K
    exact ⟨_, hϖ⟩

@[instance_reducible] private noncomputable def residueAlgebra {k K : Type u} [Field k] [Field K]
    [Algebra k K]
    (v : Valuation K ℤᵐ⁰) (hk : ∀ c : k, c ≠ 0 → v (algebraMap k K c) = 1) :
    Algebra k (IsLocalRing.ResidueField v.valuationSubring) :=
  ((IsLocalRing.residue v.valuationSubring).comp
    ((algebraMap k K).codRestrict v.valuationSubring fun c => by
      by_cases hc : c = 0
      · simp [hc]
      · exact (Valuation.mem_valuationSubring_iff _ _).2 (hk c hc).le :
      k →+* v.valuationSubring)).toAlgebra

private theorem exists_residue_family {k K : Type u} [Field k] [Field K] [Algebra k K]
    (v : Valuation K ℤᵐ⁰) (hk : ∀ c : k, c ≠ 0 → v (algebraMap k K c) = 1)
    (hfin : Algebra.trdeg k K < Cardinal.aleph0)
    (htrdeg : letI := residueAlgebra v hk;
      Algebra.trdeg k (IsLocalRing.ResidueField v.valuationSubring) + 1 = Algebra.trdeg k K) :
    ∃ (m : ℕ) (u : Fin m → v.valuationSubring),
      (letI := residueAlgebra v hk;
        AlgebraicIndependent k (fun j => IsLocalRing.residue v.valuationSubring (u j))) ∧
      (m : Cardinal) + 1 = Algebra.trdeg k K := by
  letI := residueAlgebra v hk
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k (IsLocalRing.ResidueField v.valuationSubring)
  have hcard := hs.cardinalMk_eq_trdeg
  have hlt : Cardinal.mk s < Cardinal.aleph0 := by
    rw [hcard]
    refine lt_of_le_of_lt ?_ hfin
    rw [← htrdeg]
    exact le_self_add
  have hfinite : Finite s := Cardinal.lt_aleph0_iff_finite.1 hlt
  let e : s ≃ Fin (Nat.card s) := Finite.equivFin s
  choose u hu using fun j : Fin (Nat.card s) =>
    IsLocalRing.residue_surjective (R := v.valuationSubring) (e.symm j).1
  refine ⟨Nat.card s, u, ?_, ?_⟩
  · have h1 : AlgebraicIndependent k (fun j : Fin (Nat.card s) =>
        ((e.symm j : s) : IsLocalRing.ResidueField v.valuationSubring)) :=
      hs.1.comp e.symm e.symm.injective
    convert h1 using 1
    funext j
    exact hu j
  · rw [← htrdeg, ← hcard, Nat.cast_card]

private theorem exists_common_denominator {X : Scheme.{u}} [IsIntegral X] (U : X.affineOpens)
    [Nonempty U.1] {m : ℕ} (u : Fin m → X.functionField) :
    ∃ (s : Γ(X, U.1)) (a : Fin m → Γ(X, U.1)), s ≠ 0 ∧
      ∀ j, u j * algebraMap Γ(X, U.1) X.functionField s = algebraMap _ _ (a j) := by
  have := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  obtain ⟨⟨s, hs⟩, hsa⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors Γ(X, U.1)) u
  refine ⟨s, fun j => (hsa j).choose, nonZeroDivisors.ne_zero hs, fun j => ?_⟩
  have := (hsa j).choose_spec
  simpa [Algebra.smul_def, mul_comm] using this.symm

private theorem exists_idealSheafData_ideal_eq {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U : X.affineOpens)
    (I : Ideal Γ(X, U.1)) : ∃ J : X.IdealSheafData, J.ideal U = I := by
  set f := U.2.fromSpec with hf
  have hV : f ⁻¹ᵁ U.1 = ⊤ := U.2.fromSpec_preimage_self
  have hH : IsAffineOpen (f ⁻¹ᵁ U.1) := by rw [hV]; exact isAffineOpen_top _
  set e := (Scheme.ΓSpecIso Γ(X, U.1)).inv with he
  let I' : Ideal Γ(Spec Γ(X, U.1), ⊤) := Ideal.map e.hom I
  refine ⟨(Scheme.IdealSheafData.ofIdealTop I').map f, ?_⟩
  rw [Scheme.IdealSheafData.ideal_map _ f U hH, Scheme.IdealSheafData.ofIdealTop_ideal]
  have happ : f.app U.1 = e ≫ (Spec Γ(X, U.1)).presheaf.map
      (homOfLE (le_top : f ⁻¹ᵁ U.1 ≤ ⊤)).op := by
    rw [hf, U.2.fromSpec_app_self]
    congr 2
  have hρ : Function.Bijective (CommRingCat.Hom.hom
      ((Spec Γ(X, U.1)).presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U.1 ≤ ⊤)).op)) := by
    have h : (homOfLE (le_top : f ⁻¹ᵁ U.1 ≤ ⊤)).op = eqToHom (by rw [hV]) := Subsingleton.elim _ _
    rw [h, eqToHom_map]
    exact ConcreteCategory.bijective_of_isIso _
  have he' : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e
  rw [happ, CommRingCat.hom_comp, ← Ideal.comap_comap, Ideal.comap_map_of_bijective _ hρ]
  exact Ideal.comap_map_of_bijective _ he'

/-- The ring map `Γ(X, U) → 𝒪_{T,t}` along a morphism `g : T ⟶ X`. -/
private noncomputable def rho {X T : Scheme.{u}} (g : T ⟶ X) (t : T) (U : X.affineOpens)
    (ht : g t ∈ U.1) : Γ(X, U.1) →+* T.presheaf.stalk t :=
  (g.stalkMap t).hom.comp (X.presheaf.germ U.1 (g t) ht).hom

private theorem exists_mem_map_rho_eq_span {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (z : blowUp J) (hz : blowUpToBase J z ∈ U.1) :
    ∃ a ∈ J.ideal U, Ideal.map (rho (blowUpToBase J) z U hz) (J.ideal U) =
      Ideal.span {rho (blowUpToBase J) z U hz a} := by
  obtain ⟨a, ha⟩ := exists_mem_range_blowUpAffineChart_of_mem J U z hz
  have hxa : z ∈ (blowUpChartOpen J U a).1 := by
    rw [show (blowUpChartOpen J U a).1 = (blowUpAffineChart J U a).opensRange from
      Scheme.Hom.image_top_eq_opensRange _]
    exact ha
  have hstalk := (mem_blowUpChartOpen_iff J U a z hz).mp hxa
  refine ⟨a.1, a.2, ?_⟩
  have h2 : IdealSheafData.stalk (exceptionalIdeal J) z
      = Ideal.map (rho (blowUpToBase J) z U hz) (J.ideal U) := by
    rw [show exceptionalIdeal J = J.comap (blowUpToBase J) from rfl,
      idealStalk_comap_eq_map (blowUpToBase J) J z,
      IdealSheafData.stalk_eq_map_germ J (blowUpToBase J z) U hz, Ideal.map_map]
    rfl
  rw [← h2, hstalk]
  rfl

/-- A proper morphism of integral schemes onto a Noetherian scheme which is birational in the
sense of [Stacks, Tag 01RO] is a birational morphism in the sense of rational maps. -/
private theorem isBirationalMorphism_of_isBirational {Y X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [IsIntegral Y] (f : Y ⟶ X) [IsProper f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  obtain ⟨V, hV, hiso⟩ :=
    exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian f hf
  obtain ⟨x, hx⟩ := hV.nonempty
  obtain ⟨y, rfl⟩ := surjective_of_isProper_of_isBirational f hf x
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ V) V ⟨y, hx⟩ ⟨_, hx⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact hiso

private theorem exists_model {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [hX : AlgebraicGeometry.IsVariety k sX] (J : X.IdealSheafData) (hJ : J ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ blowUp J),
      IsNormalVariety k ((ν ≫ blowUpToBase J) ≫ sX) ∧ IsProper (ν ≫ blowUpToBase J) ∧
      IsBirationalMorphism (ν ≫ blowUpToBase J) := by
  have hX0 : IsIntegral X := hX.toIsIntegral
  obtain ⟨hV, hproj, hbir⟩ :=
      MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sX J hJ
  have : LocallyOfFiniteType (blowUpToBase J ≫ sX) := hV.toLocallyOfFiniteType
  have hint : IsIntegral (blowUp J) := isIntegral_blowUp J hJ
  refine ⟨normalizationSchemeOverField k (blowUpToBase J ≫ sX),
    normalizationOverField k (blowUpToBase J ≫ sX), ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Category.assoc]
      exact isVariety_normalizationOverField k (blowUpToBase J ≫ sX)
    · exact Scheme.isNormal_normalizationScheme _ _
  · have := isFinite_normalizationOverField k (blowUpToBase J ≫ sX)
    have := hproj.isProper
    infer_instance
  · have := isFinite_normalizationOverField k (blowUpToBase J ≫ sX)
    have := hproj.isProper
    have : IsProper
        (normalizationOverField k (blowUpToBase J ≫ sX) ≫ blowUpToBase J) := inferInstance
    have : IsIntegral (normalizationSchemeOverField k (blowUpToBase J ≫ sX)) :=
      (isVariety_normalizationOverField k (blowUpToBase J ≫ sX)).toIsIntegral
    have := hX.toLocallyOfFiniteType
    have := hX.toQuasiCompact
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    have : IsNoetherian X := ⟨⟩
    exact isBirationalMorphism_of_isBirational _
      ((Scheme.isBirational_normalization (blowUp J) _).comp hbir)

private theorem exists_ne_zero_mem_maximalIdeal {Y : Scheme.{u}} [IsIntegral Y] (y : Y)
    (vY : Valuation Y.functionField ℤᵐ⁰) (hvY : Function.Surjective vY)
    (h1 : ∀ a : Y.presheaf.stalk y, vY (algebraMap _ Y.functionField a) ≤ 1) :
    ∃ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), a ≠ 0 := by
  obtain ⟨z, hz⟩ := hvY (WithZero.exp (-1))
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Y.presheaf.stalk y) z
  have hb0 : algebraMap (Y.presheaf.stalk y) Y.functionField b ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact nonZeroDivisors.ne_zero hb
  have hvb : vY (algebraMap (Y.presheaf.stalk y) Y.functionField b) ≠ 0 := by simpa using hb0
  have hvz : vY (algebraMap (Y.presheaf.stalk y) Y.functionField a) =
      WithZero.exp (-1) * vY (algebraMap (Y.presheaf.stalk y) Y.functionField b) := by
    rw [map_div₀] at hz
    rw [← hz, div_mul_cancel₀ _ hvb]
  have hlt : vY (algebraMap (Y.presheaf.stalk y) Y.functionField a) < 1 := by
    rw [hvz]
    calc WithZero.exp (-1) * vY (algebraMap (Y.presheaf.stalk y) Y.functionField b)
        ≤ WithZero.exp (-1) * 1 := by gcongr; exact h1 b
      _ < 1 := by rw [mul_one]; exact WithZero.exp_lt_one_iff.2 (by norm_num)
  refine ⟨a, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    exact hlt.ne (Valuation.Integers.one_of_isUnit' u.isUnit h1)
  · rintro rfl
    rw [map_zero, map_zero] at hvz
    exact (mul_ne_zero WithZero.exp_ne_zero hvb) hvz.symm

private theorem one_le_ringKrullDim_of_ne_zero_mem {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (ha0 : a ≠ 0) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
  rw [ringKrullDim, Order.one_le_krullDim_iff]
  refine ⟨⟨⊥, inferInstance⟩, ⟨IsLocalRing.maximalIdeal R, inferInstance⟩, ?_⟩
  show (⊥ : Ideal R) < IsLocalRing.maximalIdeal R
  rw [bot_lt_iff_ne_bot]
  intro h
  rw [h] at ha
  exact ha0 (by simpa using ha)

/-- A centre `y` of `v` on a normal model `Y` with `dim 𝒪_{Y,y} ≤ 1` is the generic point of a
prime divisor whose valuation is `v`. -/
private theorem exists_divisorOver_of_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) [IsProper f]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (v : Valuation X.functionField ℤᵐ⁰) (hv : Function.Surjective v)
    (vY : Valuation Y.functionField ℤᵐ⁰)
    (hvY : letI := hf.isDominant; ∀ x, vY (functionFieldMap f x) = v x)
    (y : Y)
    (h1 : ∀ a : Y.presheaf.stalk y, vY (algebraMap _ Y.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
      vY (algebraMap _ Y.functionField a) < 1)
    (hdim : ringKrullDim (Y.presheaf.stalk y) ≤ 1) :
    ∃ D : DivisorOver k sX, IsProper D.f ∧ D.valuation = v := by
  have := hf.isDominant
  have : IsNormal Y := IsNormalVariety.isNormal hY
  have : IsLocallyNoetherian Y := IsNormalVariety.isLocallyNoetherian hY
  have hvYs : Function.Surjective vY := by
    intro g
    obtain ⟨x, hx⟩ := hv g
    exact ⟨functionFieldMap f x, (hvY x).trans hx⟩
  obtain ⟨a, ham, ha0⟩ := exists_ne_zero_mem_maximalIdeal y vY hvYs h1
  have hge : (1 : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk y) :=
    one_le_ringKrullDim_of_ne_zero_mem a ham ha0
  have hco : Order.coheight y = 1 := by
    have h := ringKrullDim_stalk_eq_coheight y
    have : ringKrullDim (Y.presheaf.stalk y) = 1 := le_antisymm hdim hge
    rw [this] at h
    exact_mod_cast h.symm
  obtain ⟨E, rfl⟩ : ∃ E : AlgebraicGeometry.PrimeDivisor Y, E.genericPoint = y :=
    ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hco,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hco⟩
  have := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing E
  refine ⟨⟨Y, f, hY, hf, E⟩, ‹IsProper f›, ?_⟩
  have hA1 := valuation_eq_adic_of_dominated (O := MMP.Mori.PrimeDivisor.localRing E)
      (K := Y.functionField) vY hvYs h1 h2
  ext x
  show (MMP.Mori.PrimeDivisor.divisorialValuation E) (functionFieldMap f x) = v x
  rw [← hvY x, hA1]
  rfl

private theorem ringKrullDim_stalk_le_one {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sY] (y : Y) {m : ℕ}
    (w : Fin m → Y.residueField y)
    (hw : letI : Algebra k (Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
      AlgebraicIndependent k w)
    (htr : letI := functionFieldAlgebra sY
      Algebra.trdeg k Y.functionField = (m : Cardinal) + 1) :
    ringKrullDim (Y.presheaf.stalk y) ≤ 1 := by
  have := AlgebraicGeometry.IsVariety.toIsIntegral (f := sY)
  have h1 := topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y sY y
  have h2 := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y sY y
  have h3 := toENat_trdeg_functionField (sX := sY)
  letI : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  letI := functionFieldAlgebra sY
  have hK : (Cardinal.toENat (Algebra.trdeg k Y.functionField)) = ((m + 1 : ℕ) : ℕ∞) := by
    rw [htr]; simp
  have hm : (m : ℕ∞) ≤ Cardinal.toENat (Algebra.trdeg k (Y.residueField y)) := by
    have hw' : AlgebraicIndependent k (w ∘ (ULift.down : ULift.{u} (Fin m) → Fin m)) :=
      hw.comp _ ULift.down_injective
    have := hw'.cardinalMk_le_trdeg
    have h := Cardinal.toENat.monotone' this
    simpa using h
  rw [hK] at h3
  have key : ((((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) =
      (Cardinal.toENat (Algebra.trdeg k (Y.residueField y)) : WithBot ℕ∞) +
        ringKrullDim (Y.presheaf.stalk y) := by
    rw [h3, h1, h2]
  generalize (Cardinal.toENat (Algebra.trdeg k (Y.residueField y))) = t at key hm
  generalize ringKrullDim (Y.presheaf.stalk y) = d at key ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at key
  | coe e =>
    have key' : ((m + 1 : ℕ) : ℕ∞) = t + e := by
      have := key
      rw [← WithBot.coe_add] at this
      exact_mod_cast this
    have : (m : ℕ∞) + e ≤ (m : ℕ∞) + 1 := by
      calc (m : ℕ∞) + e ≤ t + e := by gcongr
        _ = _ := by rw [← key']; push_cast; rfl
    have h := (ENat.add_le_add_iff_left (ENat.natCast_ne_top m)).1 this
    exact_mod_cast h

private theorem germ_compat {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [Nonempty U] (x : X)
    (hx : x ∈ U) (c : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx c) =
      algebraMap Γ(X, U) X.functionField c := by
  show (X.presheaf.stalkSpecializes _).hom ((X.presheaf.germ U x hx).hom c) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rfl

private theorem algebraMap_rho {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (U : X.affineOpens) [Nonempty U.1] (y : Y) (hy : f y ∈ U.1) (c : Γ(X, U.1)) :
    algebraMap (Y.presheaf.stalk y) Y.functionField (rho f y U hy c) =
      functionFieldMap f (algebraMap Γ(X, U.1) X.functionField c) := by
  rw [← germ_compat U.1 (f y) hy c, functionFieldMap_algebraMap_stalk]
  rfl

/-- The key step: if `u_j = a_j / s` lie in the valuation ring of `v`, and the ideal
`(s, a_1, …, a_m)` becomes principal in the stalk `𝒪_{Y,y}` of a centre `y` of `v` on `Y`
(as it does on the blow-up of that ideal), then each `u_j` lies in `𝒪_{Y,y}`. -/
private theorem exists_stalk_lift_of_map_eq_span {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X)
    [IsDominant f] (U : X.affineOpens) [Nonempty U.1] (y : Y) (hy : f y ∈ U.1)
    (v : Valuation X.functionField ℤᵐ⁰) (vY : Valuation Y.functionField ℤᵐ⁰)
    (hvY : ∀ x, vY (functionFieldMap f x) = v x)
    {m : ℕ} (uK : Fin m → X.functionField) (s : Γ(X, U.1)) (hs0 : s ≠ 0) (a : Fin m → Γ(X, U.1))
    (hsa : ∀ j, uK j * algebraMap Γ(X, U.1) X.functionField s =
      algebraMap Γ(X, U.1) X.functionField (a j))
    (hu : ∀ j, v (uK j) ≤ 1)
    (hA : ∀ c : Γ(X, U.1), v (algebraMap Γ(X, U.1) X.functionField c) ≤ 1)
    (a0 : Γ(X, U.1)) (ha0 : a0 ∈ Ideal.span (insert s (Set.range a)))
    (hSP : Ideal.map (rho f y U hy) (Ideal.span (insert s (Set.range a))) =
      Ideal.span {rho f y U hy a0})
    (h1 : ∀ b : Y.presheaf.stalk y, vY (algebraMap _ Y.functionField b) ≤ 1)
    (h2 : ∀ b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
      vY (algebraMap _ Y.functionField b) < 1) :
    ∀ j, ∃ w : Y.presheaf.stalk y, algebraMap _ Y.functionField w = functionFieldMap f (uK j) := by
  set ι := algebraMap Γ(X, U.1) X.functionField with hι
  set φ := algebraMap (Y.presheaf.stalk y) Y.functionField with hφ
  set ρ := rho f y U hy with hρ
  have hcomp : ∀ c, φ (ρ c) = functionFieldMap f (ι c) := algebraMap_rho f U y hy
  have hvφρ : ∀ c, vY (φ (ρ c)) = v (ι c) := fun c => by rw [hcomp, hvY]
  have hιinj : Function.Injective ι := by
    have := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    exact IsFractionRing.injective _ _
  have hιs : ι s ≠ 0 := by simpa using (map_ne_zero_iff _ hιinj).2 hs0
  have hvs : v (ι s) ≠ 0 := by simpa using hιs
  -- valuation bound on the ideal
  have hI : ∀ b ∈ Ideal.span (insert s (Set.range a)), v (ι b) ≤ v (ι s) := by
    intro b hb
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · rintro b (rfl | ⟨j, rfl⟩)
      · exact le_rfl
      · rw [← hsa j, map_mul]
        calc v (uK j) * v (ι s) ≤ 1 * v (ι s) := by gcongr; exact hu j
          _ = _ := one_mul _
    · simp
    · intro b b' _ _ h h'
      rw [map_add]
      exact (Valuation.map_add _ _ _).trans (max_le h h')
    · intro r b _ h
      rw [smul_eq_mul, map_mul, map_mul]
      calc v (ι r) * v (ι b) ≤ 1 * v (ι s) := by gcongr; exact hA r
        _ = _ := one_mul _
  have hsI : s ∈ Ideal.span (insert s (Set.range a)) := Ideal.subset_span (Set.mem_insert _ _)
  have hajI : ∀ j, a j ∈ Ideal.span (insert s (Set.range a)) := fun j =>
    Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
  have hsm : ρ s ∈ Ideal.span {ρ a0} := hSP ▸ Ideal.mem_map_of_mem ρ hsI
  obtain ⟨σ, hσ⟩ := Ideal.mem_span_singleton'.1 hsm
  have hα : ∀ j, ∃ α : Y.presheaf.stalk y, α * ρ a0 = ρ (a j) := fun j =>
    Ideal.mem_span_singleton'.1 (show ρ (a j) ∈ Ideal.span {ρ a0} from
      hSP ▸ Ideal.mem_map_of_mem ρ (hajI j))
  choose α hα using hα
  have hv0 : vY (φ (ρ a0)) ≤ v (ι s) := by rw [hvφρ]; exact hI a0 ha0
  have hvσ : vY (φ σ) = 1 := by
    apply le_antisymm (h1 σ)
    have h4 : 1 * v (ι s) ≤ vY (φ σ) * v (ι s) := by
      rw [one_mul]
      calc v (ι s) = vY (φ σ) * vY (φ (ρ a0)) := by rw [← hvφρ, ← hσ, map_mul, map_mul]
        _ ≤ vY (φ σ) * v (ι s) := by gcongr
    exact le_of_mul_le_mul_right h4 (zero_lt_iff.2 hvs)
  have hσu : IsUnit σ := by
    by_contra hnu
    have := h2 σ (by rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff])
    rw [hvσ] at this
    exact lt_irrefl _ this
  have hφρa0 : φ (ρ a0) ≠ 0 := by
    intro h
    have : φ (ρ s) = 0 := by rw [← hσ, map_mul, h, mul_zero]
    rw [hcomp] at this
    have h5 : ι s = 0 := (map_eq_zero_iff _ (functionFieldMap f).injective).1 this
    exact hιs h5
  intro j
  refine ⟨α j * ↑hσu.unit⁻¹, ?_⟩
  have e1 : functionFieldMap f (uK j) * (φ σ * φ (ρ a0)) = φ (α j) * φ (ρ a0) := by
    calc functionFieldMap f (uK j) * (φ σ * φ (ρ a0))
        = functionFieldMap f (uK j) * φ (ρ s) := by rw [← hσ, map_mul]
      _ = functionFieldMap f (uK j) * functionFieldMap f (ι s) := by rw [hcomp]
      _ = functionFieldMap f (uK j * ι s) := (map_mul _ _ _).symm
      _ = functionFieldMap f (ι (a j)) := by rw [hsa j]
      _ = φ (ρ (a j)) := (hcomp _).symm
      _ = φ (α j * ρ a0) := by rw [hα j]
      _ = _ := map_mul _ _ _
  have e2 : functionFieldMap f (uK j) * φ σ = φ (α j) :=
    mul_right_cancel₀ hφρa0 ((mul_assoc _ _ _).trans e1)
  rw [map_mul, ← e2]
  have : φ (↑hσu.unit⁻¹ : Y.presheaf.stalk y) * φ σ = 1 := by
    rw [← map_mul]
    simp
  calc functionFieldMap f (uK j) * φ σ * φ ↑hσu.unit⁻¹
      = functionFieldMap f (uK j) * (φ ↑hσu.unit⁻¹ * φ σ) := by ring
    _ = _ := by rw [this, mul_one]

/-- Let `X` be a variety over `k` with function field `K`, and `v` a surjective (normalized
discrete) valuation `K → ℤᵐ⁰` trivial on `k` whose residue field has transcendence degree
`trdeg_k K - 1` over `k`. If `v` has a centre on `X`, then `v` is the valuation of a prime divisor
on a normal variety `Y` with a proper birational morphism `Y ⟶ X`. -/
@[mmp "lem_mmp_maximal_residue_dimension_divisorial"]
public theorem DivisorOver.exists_isProper_valuation_eq_of_trdeg_residueField {k : Type u}
    [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hX : IsVariety k sX)
    (v : Valuation X.functionField ℤᵐ⁰) (hv : Function.Surjective v)
    (hk : ∀ c : k, c ≠ 0 →
      v (letI := functionFieldAlgebra sX; algebraMap k X.functionField c) = 1)
    (htrdeg :
      letI := functionFieldAlgebra sX
      letI : Algebra k (IsLocalRing.ResidueField v.valuationSubring) :=
        ((IsLocalRing.residue v.valuationSubring).comp
          ((algebraMap k X.functionField).codRestrict v.valuationSubring fun c => by
            by_cases hc : c = 0
            · simp [hc]
            · exact (Valuation.mem_valuationSubring_iff _ _).2 (hk c hc).le :
            k →+* v.valuationSubring)).toAlgebra
      Algebra.trdeg k (IsLocalRing.ResidueField v.valuationSubring) + 1 =
        Algebra.trdeg k X.functionField)
    (x : X)
    (hx : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (hxm : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1) :
    ∃ D : DivisorOver k sX, IsProper D.f ∧ D.valuation = v := by
  letI : Algebra k X.functionField := functionFieldAlgebra sX
  have hfin : Algebra.trdeg k X.functionField < Cardinal.aleph0 := by
    have := essFiniteType_functionField (sX := sX)
    exact trdeg_lt_aleph0 k _
  obtain ⟨m, u, hu, hm⟩ := exists_residue_family v hk hfin htrdeg
  have : QuasiSeparatedSpace X := by
    have := hX.toIsSeparated
    exact quasiSeparatedSpace_of_isSeparated_toSpec sX this
  obtain ⟨_, ⟨U0, hU0, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U : X.affineOpens := ⟨U0, hU0⟩
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  obtain ⟨s, a, hs0, hsa⟩ :=
    exists_common_denominator U (fun j => ((u j : v.valuationSubring) : X.functionField))
  set I : Ideal Γ(X, U.1) := Ideal.span (insert s (Set.range a)) with hIdef
  obtain ⟨J, hJ⟩ := exists_idealSheafData_ideal_eq U I
  have hJbot : J ≠ ⊥ := by
    intro h
    have : s ∈ J.ideal U := by rw [hJ]; exact Ideal.subset_span (Set.mem_insert _ _)
    rw [h, Scheme.IdealSheafData.ideal_bot] at this
    exact hs0 (by simpa using this)
  obtain ⟨Y, ν, hYn, hYp, hYb⟩ := exists_model (sX := sX) J hJbot
  set π := blowUpToBase J with hπ
  set f : Y ⟶ X := ν ≫ π with hfdef
  have hYI : IsIntegral Y := IsNormalVariety.isIntegral hYn
  have hdom : IsDominant f := hYb.isDominant
  have hprop : IsProper f := hYp
  have hbij : Function.Bijective (functionFieldMap f) := hYb.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap f) hbij
  let vY : Valuation Y.functionField ℤᵐ⁰ := v.comap e.symm.toRingHom
  have hvY : ∀ z, vY (functionFieldMap f z) = v z := by
    intro z
    show v (e.symm (functionFieldMap f z)) = v z
    have : e.symm (functionFieldMap f z) = z := e.symm_apply_apply z
    rw [this]
  have hkR : ∀ c : k, (letI := functionFieldAlgebra (f ≫ sX)
      algebraMap k Y.functionField c) ∈ vY.valuationSubring := by
    intro c
    letI := functionFieldAlgebra (f ≫ sX)
    letI := functionFieldMapAlgebra f
    haveI := isScalarTower_functionFieldMap sX f
    rw [Valuation.mem_valuationSubring_iff,
        IsScalarTower.algebraMap_apply k X.functionField Y.functionField c]
    show vY (functionFieldMap f (algebraMap k X.functionField c)) ≤ 1
    rw [hvY]
    by_cases hc : c = 0
    · simp [hc]
    · exact (hk c hc).le
  have hx' : ∀ a : X.presheaf.stalk x, vY.valuationSubring.valuation
      (functionFieldMap f (algebraMap _ X.functionField a)) ≤ 1 := by
    intro a
    rw [ValuationSubring.valuation_le_one_iff, Valuation.mem_valuationSubring_iff, hvY]
    exact hx a
  have hxm' : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x), vY.valuationSubring.valuation
      (functionFieldMap f (algebraMap _ X.functionField a)) < 1 := by
    intro a ha
    refine (vY.isEquiv_valuation_valuationSubring.lt_one_iff_lt_one).1 ?_
    rw [hvY]
    exact hxm a ha
  obtain ⟨y, hyx, hy1', hy2'⟩ := exists_map_eq_and_dominates_of_isProper hX f hYn.1
    vY.valuationSubring hkR x hx' hxm'
  have hy1 : ∀ b : Y.presheaf.stalk y, vY (algebraMap _ Y.functionField b) ≤ 1 := fun b =>
    (vY.isEquiv_valuation_valuationSubring.le_one_iff_le_one).2 (hy1' b)
  have hy2 : ∀ b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
      vY (algebraMap _ Y.functionField b) < 1 := fun b hb =>
    (vY.isEquiv_valuation_valuationSubring.lt_one_iff_lt_one).2 (hy2' b hb)
  have hyU : f y ∈ U.1 := by rw [hyx]; exact hxU
  have hz : π (ν y) ∈ U.1 := hyU
  obtain ⟨a0, ha0J, hSP0⟩ := exists_mem_map_rho_eq_span J U (ν y) hz
  have ha0I : a0 ∈ I := hJ ▸ ha0J
  have hrho : rho f y U hyU = (ν.stalkMap y).hom.comp (rho π (ν y) U hz) := by
    simp only [rho, f, Scheme.Hom.stalkMap_comp]
    rfl
  have hSP : Ideal.map (rho f y U hyU) I = Ideal.span {rho f y U hyU a0} := by
    rw [hrho, ← Ideal.map_map, ← hJ, hSP0, Ideal.map_span, Set.image_singleton]
    rfl
  have hu1 : ∀ j, v ((u j : v.valuationSubring) : X.functionField) ≤ 1 := fun j =>
    (Valuation.mem_valuationSubring_iff _ _).1 (u j).2
  have hA : ∀ c : Γ(X, U.1), v (algebraMap Γ(X, U.1) X.functionField c) ≤ 1 := by
    intro c
    have := hx (X.presheaf.germ U.1 x hxU c)
    rwa [germ_compat U.1 x hxU c] at this
  have hw := exists_stalk_lift_of_map_eq_span f U y hyU v vY hvY
      (fun j => ((u j : v.valuationSubring) : X.functionField))
    s hs0 a hsa hu1 hA a0 ha0I hSP hy1 hy2
  choose w hw using hw
  -- the local homomorphism `𝒪_{Y,y} → 𝒪_v`
  let ψ : Y.presheaf.stalk y →+* v.valuationSubring :=
    ((e.symm : Y.functionField →+* X.functionField).comp
      (algebraMap (Y.presheaf.stalk y) Y.functionField)).codRestrict v.valuationSubring
      (fun b => (Valuation.mem_valuationSubring_iff _ _).2 (hy1 b))
  have hψval : ∀ b, v (ψ b : X.functionField) = vY (algebraMap _ Y.functionField b) :=
    fun b => rfl
  have hψloc : IsLocalHom ψ := by
    refine ⟨fun b hb => ?_⟩
    by_contra hnu
    have hlt := hy2 b (by rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff])
    have h1 := (ValuationSubring.valuation_eq_one_iff v.valuationSubring (ψ b)).1 hb
    have h2 : v (ψ b : X.functionField) < 1 := by rw [hψval]; exact hlt
    have h3 := (v.isEquiv_valuation_valuationSubring.lt_one_iff_lt_one).1 h2
    rw [h1] at h3
    exact lt_irrefl _ h3
  haveI := hψloc
  let g0 : IsLocalRing.ResidueField (Y.presheaf.stalk y) →+*
      IsLocalRing.ResidueField v.valuationSubring := IsLocalRing.ResidueField.map ψ
  have hg0 : ∀ b, g0 (IsLocalRing.residue _ b) = IsLocalRing.residue _ (ψ b) := fun b =>
    IsLocalRing.ResidueField.map_residue ψ b
  have hψw : ∀ j, ψ (w j) = u j := fun j => Subtype.ext (by
    show e.symm (algebraMap _ Y.functionField (w j)) = _
    rw [hw j]; exact e.symm_apply_apply _)
  letI instκy : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫ Y.Γevaluation y).hom.toAlgebra
  letI instκv : Algebra k (IsLocalRing.ResidueField v.valuationSubring) := residueAlgebra v hk
  have hcomm : ∀ c : k, g0 (algebraMap k (Y.residueField y) c) =
      algebraMap k (IsLocalRing.ResidueField v.valuationSubring) c := by
    intro c
    let bc : Y.presheaf.stalk y :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫ Y.presheaf.germ ⊤ y trivial).hom c
    have h1 : algebraMap k (Y.residueField y) c = IsLocalRing.residue _ bc := rfl
    rw [h1, hg0]
    have h2 : (ψ bc : X.functionField) = algebraMap k X.functionField c := by
      show e.symm (algebraMap _ Y.functionField bc) = _
      letI := functionFieldAlgebra (f ≫ sX)
      letI := stalkAlgebra (f ≫ sX) y
      letI := functionFieldMapAlgebra f
      haveI := isScalarTower_functionFieldMap sX f
      haveI := isScalarTower_stalk_functionField (f ≫ sX) y
      have h3 : algebraMap
          (Y.presheaf.stalk y) Y.functionField bc = algebraMap k Y.functionField c := by
        rw [IsScalarTower.algebraMap_apply k (Y.presheaf.stalk y) Y.functionField c]
        rfl
      rw [h3, IsScalarTower.algebraMap_apply k X.functionField Y.functionField c]
      exact e.symm_apply_apply _
    exact congrArg (IsLocalRing.residue _) (Subtype.ext h2)
  let g : Y.residueField y →ₐ[k] IsLocalRing.ResidueField v.valuationSubring :=
    { g0 with commutes' := hcomm }
  let wr : Fin m → Y.residueField y := fun j => IsLocalRing.residue (Y.presheaf.stalk y) (w j)
  have hind : AlgebraicIndependent k wr := by
    refine AlgebraicIndependent.of_comp g ?_
    have : (g ∘ wr) =
        fun j => IsLocalRing.residue v.valuationSubring (u j) := by
      funext j
      show g0 _ = _
      rw [hg0, hψw]
    rw [this]
    exact hu
  have htr : letI := functionFieldAlgebra (f ≫ sX)
      Algebra.trdeg k Y.functionField = (m : Cardinal) + 1 := by
    letI := functionFieldAlgebra (f ≫ sX)
    rw [← trdeg_functionField_eq_of_bijective sX f hbij, hm]
  have hdim : ringKrullDim (Y.presheaf.stalk y) ≤ 1 := by
    haveI := hYn.1
    exact ringKrullDim_stalk_le_one (sY := f ≫ sX) y wr hind htr
  exact exists_divisorOver_of_stalk f hYn hYb v hv vY hvY y hy1 hy2 hdim

end MMP.Mori

namespace MMP.Flips

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite IsLocalRing MMP.Mori
open MMP.Flips.Normalization
  MMP.Flips.SingLoc
open scoped TensorProduct

private theorem appLE_congr {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V h₁ = g.appLE U V h₂ := by
  subst e; rfl

/-- Two morphisms `a b : X ⟶ Y` that agree after composing with `ν : Y ⟶ Z` pull back sections
coming from `Z` in the same way. -/
private theorem appLE_app_eq_of_comp_eq {X Y Z : Scheme} (a b : X ⟶ Y) (ν : Y ⟶ Z)
    (e : a ≫ ν = b ≫ ν) (U : Z.Opens) (W : X.Opens) (h₁ : W ≤ a ⁻¹ᵁ (ν ⁻¹ᵁ U))
    (h₂ : W ≤ b ⁻¹ᵁ (ν ⁻¹ᵁ U)) (f : Γ(Z, U)) :
    (a.appLE (ν ⁻¹ᵁ U) W h₁).hom ((ν.app U).hom f) =
      (b.appLE (ν ⁻¹ᵁ U) W h₂).hom ((ν.app U).hom f) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appLE a ν U W h₁,
    ← Scheme.Hom.comp_appLE b ν U W h₂]
  exact congrArg (fun φ => φ.hom f) (appLE_congr e U W h₁ h₂)

section Generic

private theorem preimage_eq {Y S E D : Scheme.{0}} (ν : Y ⟶ S) (ι : E ⟶ Y) (κ : D ⟶ S) (π : E ⟶ D)
    (hπ : π ≫ κ = ι ≫ ν) (V : S.Opens) : π ⁻¹ᵁ (κ ⁻¹ᵁ V) = ι ⁻¹ᵁ (ν ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, hπ, Scheme.Hom.comp_preimage]

variable {Y S E D : Scheme.{0}} (ν : Y ⟶ S) (ι : E ⟶ Y) (κ : D ⟶ S) (π : E ⟶ D) (τ : E ⟶ E)

private theorem app_restrict {V V' : S.Opens} (i : V' ⟶ V) (x : Γ(S, V)) :
    (ν.app V').hom (S.presheaf.map i.op x) =
      Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono ν i.le)).op ((ν.app V).hom x) := by
  have := ν.naturality i.op
  have h2 := ConcreteCategory.congr_hom this x
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h2
  exact h2

private theorem range_of_local (inj : ∀ V : S.Opens, Function.Injective (ν.app V).hom)
    (U : S.Opens) (g : Γ(Y, ν ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (U' : S.Opens) (hU' : U' ≤ U), x ∈ U' ∧
      Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono ν hU')).op g ∈ Set.range (ν.app U').hom) :
    g ∈ Set.range (ν.app U).hom := by
  classical
  choose! W hWU hxW hf using h
  choose f hf using hf
  let I := {x : S // x ∈ U}
  have hcover : U ≤ iSup (fun i : I => W i.1) := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW x hx⟩
  let sf : ∀ i : I, S.presheaf.obj (op (W i.1)) := fun i => f i.1 i.2
  have hcompat : TopCat.Presheaf.IsCompatible S.presheaf (fun i : I => W i.1) sf := by
    intro i j
    apply inj
    rw [app_restrict, app_restrict, hf, hf]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Y.presheaf.map_comp,
      ← Y.presheaf.map_comp]
    rfl
  obtain ⟨s, hs, -⟩ := S.sheaf.existsUnique_gluing' (fun i : I => W i.1) U
    (fun i => homOfLE (hWU i.1 i.2)) hcover sf hcompat
  refine ⟨s, ?_⟩
  refine (Y.sheaf.eq_of_locally_eq' (fun i : I => ν ⁻¹ᵁ (W i.1)) (ν ⁻¹ᵁ U)
    (fun i => homOfLE (Scheme.Hom.preimage_mono ν (hWU i.1 i.2))) ?_ _ _ ?_)
  · intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨ν x, hx⟩, hxW _ hx⟩
  · intro i
    have e : (Y.sheaf.obj.map (homOfLE (Scheme.Hom.preimage_mono ν (hWU i.1 i.2))).op).hom
        ((ν.app U).hom s)
        = Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono ν (hWU i.1 i.2))).op
          ((ν.app U).hom s) := rfl
    rw [e]
    have := app_restrict ν (homOfLE (hWU i.1 i.2)) s
    rw [← this]
    have hs' : S.presheaf.map (homOfLE (hWU i.1 i.2)).op s = sf i := hs i
    rw [hs']
    exact hf i.1 i.2
private theorem range_of_cover (inj : ∀ V : S.Opens, Function.Injective (ν.app V).hom)
    (U : S.Opens) (g : Γ(Y, ν ⁻¹ᵁ U))
    (h : ∀ (V : S.affineOpens) (hV : V.1 ≤ U),
      Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono ν hV)).op g ∈ Set.range (ν.app V).hom) :
    g ∈ Set.range (ν.app U).hom := by
  refine range_of_local ν inj U g fun x hx => ?_
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (show x ∈ U from hx)
  exact ⟨V, hVU, hxV, h ⟨V, hV⟩ hVU⟩

private theorem exists_local_of_closed [JacobsonSpace S] (V : S.Opens) (g : Γ(Y, ν ⁻¹ᵁ V))
    (hc : ∀ x ∈ V, IsClosed ({x} : Set S) → ∃ (U' : S.Opens) (hU' : U' ≤ V), x ∈ U' ∧
      Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono ν hU')).op g ∈ Set.range (ν.app U').hom)
    (x : S) (hx : x ∈ V) : ∃ (U' : S.Opens) (hU' : U' ≤ V), x ∈ U' ∧
      Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono ν hU')).op g ∈ Set.range
          (ν.app U').hom := by
  let G : Set S := {y | ∃ (U' : S.Opens) (hU' : U' ≤ V), y ∈ U' ∧
      Y.presheaf.map (homOfLE (Scheme.Hom.preimage_mono ν hU')).op g ∈ Set.range (ν.app U').hom}
  have hGo : IsOpen G := by
    refine isOpen_iff_forall_mem_open.mpr fun y hy => ?_
    obtain ⟨U', hU', hyU', hr⟩ := hy
    refine ⟨U', fun z hz => ⟨U', hU', hz, hr⟩, U'.isOpen, hyU'⟩
  by_contra hxG
  have hZ : IsLocallyClosed ((V : Set S) ∩ Gᶜ) :=
    ⟨V, Gᶜ, V.isOpen, hGo.isClosed_compl, rfl⟩
  obtain ⟨z, ⟨hzV, hzG⟩, hzc⟩ := nonempty_inter_closedPoints
      (show ((V : Set S) ∩ Gᶜ).Nonempty from ⟨x, hx, hxG⟩) hZ
  exact hzG (hc z hzV hzc)
private theorem app_eq_zero_of_appLE {U' : Y.Opens} {W : E.Opens} (e : W = ι ⁻¹ᵁ U')
    (h : W ≤ ι ⁻¹ᵁ U') (g : Γ(Y, U')) (hg : (ι.appLE U' W h).hom g = 0) :
    (ι.app U').hom g = 0 := by
  subst e; rwa [Scheme.Hom.appLE_eq_app] at hg

private theorem range_of_affine (hπ : π ≫ κ = ι ≫ ν)
    (hκ : ∀ V : S.affineOpens, Function.Surjective (κ.app V))
    (core : ∀ V : S.affineOpens, ∀ g : Γ(Y, ν ⁻¹ᵁ V), (ι.app (ν ⁻¹ᵁ V)).hom g = 0 →
      g ∈ Set.range (ν.app V).hom)
    (V : S.affineOpens) (g : Γ(Y, ν ⁻¹ᵁ V))
    (hd : ∃ d : Γ(D, κ ⁻¹ᵁ V), (π.app (κ ⁻¹ᵁ V)).hom d =
      (ι.appLE (ν ⁻¹ᵁ V) (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) (preimage_eq ν ι κ π hπ V).le).hom g) :
    g ∈ Set.range (ν.app V).hom := by
  obtain ⟨d, hd⟩ := hd
  obtain ⟨f, rfl⟩ := hκ V d
  have key : (ι.appLE (ν ⁻¹ᵁ V) (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) (preimage_eq ν ι κ π hπ V).le).hom
      ((ν.app V).hom f) =
      (ι.appLE (ν ⁻¹ᵁ V) (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) (preimage_eq ν ι κ π hπ V).le).hom g := by
    rw [← hd]
    have e1 : (π.app (κ ⁻¹ᵁ V)).hom ((κ.app V).hom f)
        = ((π ≫ κ).appLE V (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) (by rw [Scheme.Hom.comp_preimage])).hom f := by
      rw [Scheme.Hom.comp_appLE, ← Scheme.Hom.app_eq_appLE]; rfl
    have e2 :
        ((ι ≫ ν).appLE V (π ⁻¹ᵁ (κ ⁻¹ᵁ V))
        (by rw [Scheme.Hom.comp_preimage, ← preimage_eq ν ι κ π hπ V])).hom f
        = (ι.appLE (ν ⁻¹ᵁ V) (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) (preimage_eq ν ι κ π hπ V).le).hom
            ((ν.app V).hom f) := by
      rw [Scheme.Hom.comp_appLE]; rfl
    rw [e1, ← e2]
    rw [appLE_congr hπ V (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) _
        (by rw [Scheme.Hom.comp_preimage, ← preimage_eq ν ι κ π hπ V])]
  obtain ⟨f', hf'⟩ := core V (g - (ν.app V).hom f) (app_eq_zero_of_appLE ι
    (preimage_eq ν ι κ π hπ V) (preimage_eq ν ι κ π hπ V).le _
    (by rw [map_sub, key, sub_self]))
  exact ⟨f + f', by rw [map_add, hf']; abel⟩

private theorem exists_of_invariant (hπ : π ≫ κ = ι ≫ ν)
    (hτ : ∀ (V : D.Opens) (h : Γ(E, π ⁻¹ᵁ V)),
      h ∈ Set.range (π.app V).hom ↔
        ∀ (W : E.Opens) (h₁ : W ≤ π ⁻¹ᵁ V) (h₂ : W ≤ τ ⁻¹ᵁ (π ⁻¹ᵁ V)),
          (E.presheaf.map (homOfLE h₁).op).hom h = (τ.appLE (π ⁻¹ᵁ V) W h₂).hom h)
    (V : S.Opens) (g : Γ(Y, ν ⁻¹ᵁ V))
    (H : ∀ (W : E.Opens) (h₁ : W ≤ ι ⁻¹ᵁ (ν ⁻¹ᵁ V)) (h₂ : W ≤ (τ ≫ ι) ⁻¹ᵁ (ν ⁻¹ᵁ V)),
        (ι.appLE _ W h₁).hom g = ((τ ≫ ι).appLE _ W h₂).hom g) :
    ∃ d : Γ(D, κ ⁻¹ᵁ V), (π.app (κ ⁻¹ᵁ V)).hom d =
      (ι.appLE (ν ⁻¹ᵁ V) (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) (preimage_eq ν ι κ π hπ V).le).hom g := by
  have := (hτ (κ ⁻¹ᵁ V)
      ((ι.appLE (ν ⁻¹ᵁ V) (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) (preimage_eq ν ι κ π hπ V).le).hom g)).mpr
  apply this
  intro W h₁ h₂
  have hW1 : W ≤ ι ⁻¹ᵁ (ν ⁻¹ᵁ V) := h₁.trans (preimage_eq ν ι κ π hπ V).le
  have hW2 : W ≤ (τ ≫ ι) ⁻¹ᵁ (ν ⁻¹ᵁ V) := by
    rw [Scheme.Hom.comp_preimage, ← preimage_eq ν ι κ π hπ V]; exact h₂
  have e1 : (E.presheaf.map (homOfLE h₁).op).hom
      ((ι.appLE (ν ⁻¹ᵁ V) (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) (preimage_eq ν ι κ π hπ V).le).hom g) =
      (ι.appLE (ν ⁻¹ᵁ V) W hW1).hom g := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have e2 : (τ.appLE (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) W h₂).hom
      ((ι.appLE (ν ⁻¹ᵁ V) (π ⁻¹ᵁ (κ ⁻¹ᵁ V)) (preimage_eq ν ι κ π hπ V).le).hom g) =
      ((τ ≫ ι).appLE (ν ⁻¹ᵁ V) W hW2).hom g := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [e1, e2]
  exact H W hW1 hW2

private theorem range_of_invariant (hπ : π ≫ κ = ι ≫ ν)
    (inj : ∀ V : S.Opens, Function.Injective (ν.app V).hom)
    (hκ : ∀ V : S.affineOpens, Function.Surjective (κ.app V))
    (core : ∀ V : S.affineOpens, ∀ g : Γ(Y, ν ⁻¹ᵁ V), (ι.app (ν ⁻¹ᵁ V)).hom g = 0 →
      g ∈ Set.range (ν.app V).hom)
    (hτ : ∀ (V : D.Opens) (h : Γ(E, π ⁻¹ᵁ V)),
      h ∈ Set.range (π.app V).hom ↔
        ∀ (W : E.Opens) (h₁ : W ≤ π ⁻¹ᵁ V) (h₂ : W ≤ τ ⁻¹ᵁ (π ⁻¹ᵁ V)),
          (E.presheaf.map (homOfLE h₁).op).hom h = (τ.appLE (π ⁻¹ᵁ V) W h₂).hom h)
    (U : S.Opens) (g : Γ(Y, ν ⁻¹ᵁ U))
    (H : ∀ (W : E.Opens) (h₁ : W ≤ ι ⁻¹ᵁ (ν ⁻¹ᵁ U)) (h₂ : W ≤ (τ ≫ ι) ⁻¹ᵁ (ν ⁻¹ᵁ U)),
        (ι.appLE _ W h₁).hom g = ((τ ≫ ι).appLE _ W h₂).hom g) :
    g ∈ Set.range (ν.app U).hom := by
  refine range_of_cover ν inj U g fun V hV => ?_
  have hVU : ν ⁻¹ᵁ V.1 ≤ ν ⁻¹ᵁ U := Scheme.Hom.preimage_mono ν hV
  refine range_of_affine ν ι κ π hπ hκ core V _ ?_
  refine exists_of_invariant ν ι κ π τ hπ hτ V.1 _ ?_
  intro W h₁ h₂
  have hW1 : W ≤ ι ⁻¹ᵁ (ν ⁻¹ᵁ U) := h₁.trans (Scheme.Hom.preimage_mono ι hVU)
  have hW2 : W ≤ (τ ≫ ι) ⁻¹ᵁ (ν ⁻¹ᵁ U) := h₂.trans (Scheme.Hom.preimage_mono _ hVU)
  have e1 : (ι.appLE (ν ⁻¹ᵁ V.1) W h₁).hom (Y.presheaf.map (homOfLE hVU).op g) =
      (ι.appLE (ν ⁻¹ᵁ U) W hW1).hom g := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have e2 : ((τ ≫ ι).appLE (ν ⁻¹ᵁ V.1) W h₂).hom (Y.presheaf.map (homOfLE hVU).op g) =
      ((τ ≫ ι).appLE (ν ⁻¹ᵁ U) W hW2).hom g := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rw [e1, e2]
  exact H W hW1 hW2

end Generic

/-! ### Descent along the completion (step 4) -/

private theorem mem_range_of_tmul_eq {A A' C : Type*} [CommRing A] [CommRing A'] [CommRing C]
    [Algebra A A'] [Algebra A C] [Module.FaithfullyFlat A C] (a' : A')
    (h : ∃ y : C, a' ⊗ₜ[A] (1 : C) = (1 : A') ⊗ₜ[A] y) :
    a' ∈ Set.range (algebraMap A A') := by
  obtain ⟨y, hy⟩ := h
  let q : A' →ₗ[A] A' ⧸ (Algebra.linearMap A A').range := Submodule.mkQ _
  have h1 : (q a') ⊗ₜ[A] (1 : C) = 0 := by
    have := congrArg (LinearMap.rTensor C q) hy
    simp only [LinearMap.rTensor_tmul] at this
    rw [this]
    have : q 1 = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨1, by simp⟩
    rw [this, TensorProduct.zero_tmul]
  have h2 : (1 : C) ⊗ₜ[A] (q a') = 0 := by
    have := congrArg (TensorProduct.comm A (A' ⧸ (Algebra.linearMap A A').range) C) h1
    simpa using this
  have h3 := (Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := A) (A := C)
    (M := A' ⧸ (Algebra.linearMap A A').range) (q a')).mp h2
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h3
  obtain ⟨r, hr⟩ := h3
  exact ⟨r, hr⟩

private theorem faithfullyFlat_adicCompletion (A : Type*) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) := by
  have : Module.Flat A (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.flat_of_isNoetherian (maximalIdeal A)
  have : IsLocalRing (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.isLocalRing_of_fg (IsNoetherian.noetherian _)
  have : IsLocalHom (algebraMap A (AdicCompletion (maximalIdeal A) A)) :=
    AdicCompletion.instIsLocalHomMaximalIdealRingHomAlgebraMapOfIsNoetherianRing
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-! ### Regular case (step 3) -/

private theorem surjective_algebraMap_of_isIntegrallyClosed {A A' : Type*} [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [CommRing A'] [Algebra A A']
    (e : A' ≃ₐ[A] integralClosure A (FractionRing A)) :
    Function.Surjective (algebraMap A A') := by
  intro a'
  have h : (e a' : FractionRing A) ∈ (⊥ : Subalgebra A (FractionRing A)) := by
    have := (IsIntegrallyClosedIn.integralClosure_eq_bot_iff (FractionRing A) (R := A)
      (IsFractionRing.injective A (FractionRing A))).mpr ‹_›
    rw [← this]; exact (e a').2
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp h
  refine ⟨r, e.injective (Subtype.ext ?_)⟩
  simpa using hr

private theorem surjective_algebraMap_of_isRegularLocalRing {A A' : Type*} [CommRing A]
    [IsLocalRing A] [CommRing A'] [Algebra A A'] (hA : IsRegularLocalRing A)
    (e : A' ≃ₐ[A] integralClosure A (FractionRing A)) :
    Function.Surjective (algebraMap A A') := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : UniqueFactorizationMonoid A := IsRegularLocalRing.uniqueFactorizationMonoid A
  exact surjective_algebraMap_of_isIntegrallyClosed e

/-! ### Even and odd parts of a power series -/

section EvenOdd

open PowerSeries

variable {B : Type*} [CommRing B]

/-- A power series is the sum of its even part and `X` times its odd part. -/
private theorem expand_two_add_X_mul_expand_two (f : B⟦X⟧) :
    expand 2 two_ne_zero (mk fun j => coeff (2 * j) f) +
      PowerSeries.X * expand 2 two_ne_zero (mk fun j => coeff (2 * j + 1) f) = f := by
  ext n
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [map_add, show j + j = 2 * j by ring, coeff_expand_mul]
    rcases j with _ | j
    · simp
    · rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, coeff_succ_X_mul,
        coeff_expand_of_not_dvd _ _ _ (by omega)]
      simp [show 2 * (j + 1) = (2 * j + 1) + 1 by ring]
  · rw [map_add, coeff_succ_X_mul, coeff_expand_mul, coeff_expand_of_not_dvd _ _ _ (by omega)]
    simp

end EvenOdd

section PinchRadical

open PowerSeries

private theorem prime_C_X_zero :
    Prime (PowerSeries.C (MvPowerSeries.X 0 : MvPowerSeries (Fin (0 + 1)) ℂ) :
      (MvPowerSeries (Fin (0 + 1)) ℂ)⟦X⟧) := by
  have h : Prime (MvPowerSeries.X 1 : MvPowerSeries (Fin (1 + 1)) ℂ) := prime_X 1
  let eq := MvPowerSeries.finSuccEquiv ℂ 1
  have : eq (MvPowerSeries.X 1) = PowerSeries.C (MvPowerSeries.X 0) :=
    MvPowerSeries.finSuccEquiv_X_succ (j := 0)
  rw [← this]
  exact (MulEquiv.prime_iff eq.toMulEquiv).mpr h

/-- Every multiple `C b * c` lies in the image of the pinch ring: split `c` into its even and
odd parts. -/
private theorem C_mul_mem_range_pinchMap {B : Type*} [CommRing B] (b : B) (c : B⟦X⟧) :
    PowerSeries.C b * c ∈ Set.range (pinchMap b) := by
  rw [← expand_two_add_X_mul_expand_two c]
  refine ⟨Ideal.Quotient.mk _ (Polynomial.C (PowerSeries.C b * mk fun j => coeff (2 * j) c)) +
    Ideal.Quotient.mk _ Polynomial.X *
      Ideal.Quotient.mk _ (Polynomial.C (mk fun j => coeff (2 * j + 1) c)), ?_⟩
  simp only [map_add, map_mul, pinchMap_mk_C, pinchMap_mk_X, expand_C]
  ring

private theorem pinch_radical_mem_range (E : Type) [CommRing E]
    (e : E ≃+* (MvPowerSeries (Fin 3) ℂ ⧸
      Ideal.span {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin 3) ℂ)}))
    (z : integralClosure E (FractionRing E))
    (hz : z ∈ (Ideal.map (algebraMap E (integralClosure E (FractionRing E)))
      (Ideal.comap e.toRingHom (Ideal.span {Ideal.Quotient.mk _ (MvPowerSeries.X 0),
        Ideal.Quotient.mk _ (MvPowerSeries.X 2)}))).radical) :
    z ∈ Set.range (algebraMap E (integralClosure E (FractionRing E))) := by
  set B := MvPowerSeries (Fin (0 + 1)) ℂ with hB
  set b : B := MvPowerSeries.X 0 with hb'
  have : IsRegularLocalRing B := MvPowerSeries.isRegularLocalRing ℂ (0 + 1)
  have : IsDomain B := IsRegularLocalRing.isDomain B
  have hb : b ≠ 0 := fun h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h
    simp [b, MvPowerSeries.coeff_X] at this
  let ι : (MvPowerSeries (Fin 3) ℂ ⧸
      Ideal.span {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin 3) ℂ)}) ≃+* PinchRing b := (pinchModelEquiv ℂ 0).toRingEquiv
  let f : E ≃+* PinchRing b := e.trans ι
  let ψ : E →+* B⟦X⟧ := (pinchMap b).comp f.toRingHom
  have hψinj : Function.Injective ψ := (pinchMap_injective b hb).comp f.injective
  have : IsDomain E := hψinj.isDomain ψ
  have : IsRegularLocalRing B⟦X⟧ := PowerSeries.isRegularLocalRing B
  have : IsDomain B⟦X⟧ := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid B⟦X⟧ := IsRegularLocalRing.uniqueFactorizationMonoid _
  let : Algebra E B⟦X⟧ := ψ.toAlgebra
  have : FaithfulSMul E B⟦X⟧ := (faithfulSMul_iff_algebraMap_injective _ _).2 hψinj
  have hint : Algebra.IsIntegral E B⟦X⟧ := ⟨fun c => by
    obtain ⟨p, hp, hpc⟩ := pinchMap_isIntegralElem b c
    refine ⟨p.map f.symm.toRingHom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap E B⟦X⟧).comp f.symm.toRingHom = pinchMap b :=
      RingHom.ext fun r => by
        show ψ (f.symm r) = _
        simp [ψ]
    rw [hcomp]
    exact hpc⟩
  have hbir : ∀ c : B⟦X⟧, ∃ r s : E, s ≠ 0 ∧ algebraMap E B⟦X⟧ s * c = algebraMap E B⟦X⟧ r := by
    intro c
    obtain ⟨r, s, hs, h⟩ := pinchMap_birational hb c
    refine ⟨f.symm r, f.symm s, ?_, ?_⟩
    · intro h0
      apply hs
      have : s = f (f.symm s) := (f.apply_symm_apply s).symm
      rw [this, h0, map_zero, map_zero]
    · show ψ (f.symm s) * c = ψ (f.symm r)
      simpa [ψ] using h
  have : IsIntegrallyClosed (integralClosure E (FractionRing E)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing E) (L := FractionRing E)
  have hL : ∀ l : integralClosure E (FractionRing E), ∃ r s : E, s ≠ 0 ∧
      algebraMap E (integralClosure E (FractionRing E)) s * l =
        algebraMap E (integralClosure E (FractionRing E)) r := by
    intro l
    obtain ⟨a, d, hd, h⟩ := IsFractionRing.div_surjective (A := E) (l : FractionRing E)
    refine ⟨a, d, nonZeroDivisors.ne_zero hd, Subtype.ext ?_⟩
    have hd' : algebraMap E (FractionRing E) d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective E _)).2 (nonZeroDivisors.ne_zero hd)
    show algebraMap E (FractionRing E) d * (l : FractionRing E) =
      algebraMap E (FractionRing E) a
    rw [← h]
    field_simp
  obtain ⟨σ⟩ := nonempty_algEquiv_of_isIntegrallyClosed_of_birational E
      (integralClosure E (FractionRing E)) B⟦X⟧ hL hbir
  have hσ : ∀ r : E, σ (algebraMap E (integralClosure E (FractionRing E)) r) = ψ r :=
      fun r => σ.commutes r
  have hι0 : pinchMap b (ι (Ideal.Quotient.mk _ (MvPowerSeries.X 0))) =
      PowerSeries.X * PowerSeries.C b := by
    show pinchMap b (pinchModelEquiv ℂ 0 _) = _
    rw [pinchModelEquiv_mk_X_zero, pinchMap_mk_X]
  have hι2 : pinchMap b (ι (Ideal.Quotient.mk _ (MvPowerSeries.X 2))) = PowerSeries.C b := by
    show pinchMap b (pinchModelEquiv ℂ 0 _) = _
    rw [pinchModelEquiv_mk_X_two, pinchMap_mk_C, expand_C]
  have hP : ∀ p : E, e p ∈ Ideal.span {(Ideal.Quotient.mk _ (MvPowerSeries.X 0) :
      MvPowerSeries (Fin 3) ℂ ⧸ _), Ideal.Quotient.mk _ (MvPowerSeries.X 2)} →
      ψ p ∈ Ideal.span {(PowerSeries.C b : B⟦X⟧)} := by
    intro p hp
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hp
    have e1 : ψ p = pinchMap b (ι (e p)) := rfl
    have : ψ p = pinchMap b (ι α) * (PowerSeries.X * PowerSeries.C b) +
        pinchMap b (ι β) * PowerSeries.C b := by
      rw [e1, ← hαβ, map_add, map_mul, map_mul, map_add, map_mul, map_mul, hι0, hι2]
    rw [this, Ideal.mem_span_singleton]
    exact dvd_add (Dvd.dvd.mul_left ⟨PowerSeries.X, by ring⟩ _) (Dvd.intro_left _ rfl)
  obtain ⟨m, hm⟩ := hz
  have hle : Ideal.map (algebraMap E (integralClosure E (FractionRing E)))
      (Ideal.comap e.toRingHom (Ideal.span
        {Ideal.Quotient.mk _ (MvPowerSeries.X 0), Ideal.Quotient.mk _ (MvPowerSeries.X 2)})) ≤
      Ideal.comap σ.toRingEquiv.toRingHom (Ideal.span {(PowerSeries.C b : B⟦X⟧)}) := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_comap]
    exact (hσ p).symm ▸ hP p hp
  have h1 : σ z ^ m ∈ Ideal.span {(PowerSeries.C b : B⟦X⟧)} := by
    have := hle hm
    rw [Ideal.mem_comap] at this
    simpa using this
  obtain ⟨c, hc⟩ := prime_C_X_zero.dvd_of_dvd_pow (Ideal.mem_span_singleton.mp h1)
  obtain ⟨r', hr'⟩ := C_mul_mem_range_pinchMap b c
  rw [← hc] at hr'
  refine ⟨f.symm r', σ.injective ?_⟩
  rw [hσ]
  show pinchMap b (f (f.symm r')) = _
  rw [f.apply_symm_apply]
  exact hr'

private theorem pinch_isPrime (E : Type) [CommRing E]
    (e : E ≃+* (MvPowerSeries (Fin 3) ℂ ⧸
      Ideal.span {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin 3) ℂ)})) :
    (Ideal.comap e.toRingHom (Ideal.span {Ideal.Quotient.mk _ (MvPowerSeries.X 0),
        Ideal.Quotient.mk _ (MvPowerSeries.X 2)})).IsPrime := by
  set B := MvPowerSeries (Fin (0 + 1)) ℂ with hB
  set b : B := MvPowerSeries.X 0 with hb'
  have : IsRegularLocalRing B := MvPowerSeries.isRegularLocalRing ℂ (0 + 1)
  have : IsDomain B := IsRegularLocalRing.isDomain B
  have hb : b ≠ 0 := fun h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h
    simp [b, MvPowerSeries.coeff_X] at this
  let ι : (MvPowerSeries (Fin 3) ℂ ⧸
      Ideal.span {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin 3) ℂ)}) ≃+* PinchRing b := (pinchModelEquiv ℂ 0).toRingEquiv
  let f : E ≃+* PinchRing b := e.trans ι
  let ψ : E →+* B⟦X⟧ := (pinchMap b).comp f.toRingHom
  have hψinj : Function.Injective ψ := (pinchMap_injective b hb).comp f.injective
  have hι0 : pinchMap b (ι (Ideal.Quotient.mk _ (MvPowerSeries.X 0))) =
      PowerSeries.X * PowerSeries.C b := by
    show pinchMap b (pinchModelEquiv ℂ 0 _) = _
    rw [pinchModelEquiv_mk_X_zero, pinchMap_mk_X]
  have hι2 : pinchMap b (ι (Ideal.Quotient.mk _ (MvPowerSeries.X 2))) = PowerSeries.C b := by
    show pinchMap b (pinchModelEquiv ℂ 0 _) = _
    rw [pinchModelEquiv_mk_X_two, pinchMap_mk_C, expand_C]
  have hP : Ideal.comap e.toRingHom (Ideal.span {Ideal.Quotient.mk _ (MvPowerSeries.X 0),
        Ideal.Quotient.mk _ (MvPowerSeries.X 2)}) =
      Ideal.comap ψ (Ideal.span {(PowerSeries.C b : B⟦X⟧)}) := by
    ext p
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_span_singleton]
    constructor
    · intro hp
      obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hp
      have e1 : ψ p = pinchMap b (ι (e p)) := rfl
      have : ψ p = pinchMap b (ι α) * (PowerSeries.X * PowerSeries.C b) +
          pinchMap b (ι β) * PowerSeries.C b := by
        rw [e1]
        have h2 : e.toRingHom p = e p := rfl
        rw [← h2, ← hαβ, map_add, map_mul, map_mul, map_add, map_mul, map_mul, hι0, hι2]
      rw [this]
      exact dvd_add (Dvd.dvd.mul_left ⟨PowerSeries.X, by ring⟩ _) (Dvd.intro_left _ rfl)
    · rintro ⟨c, hc⟩
      obtain ⟨a₀, a₁, hdec⟩ : ∃ a₀ a₁ : B⟦X⟧, expand 2 two_ne_zero a₀ +
          PowerSeries.X * expand 2 two_ne_zero a₁ = c :=
        ⟨_, _, expand_two_add_X_mul_expand_two c⟩
      let r' : PinchRing b := Ideal.Quotient.mk _ (Polynomial.C (PowerSeries.C b * a₀)) +
        Ideal.Quotient.mk _ Polynomial.X * Ideal.Quotient.mk _ (Polynomial.C a₁)
      have hr' : pinchMap b r' = ψ p := by
        rw [hc, ← hdec]
        simp only [r', map_add, map_mul, pinchMap_mk_C, pinchMap_mk_X, expand_C]
        ring
      have hpr : p = f.symm r' := by
        apply hψinj
        show ψ p = pinchMap b (f (f.symm r'))
        rw [f.apply_symm_apply, hr']
      have hep : e p = ι.symm r' := by
        have : f.symm r' = e.symm (ι.symm r') := rfl
        rw [hpr, this, e.apply_symm_apply]
      have hk0 : ι (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = Ideal.Quotient.mk _ Polynomial.X :=
        pinchModelEquiv_mk_X_zero ℂ 0
      have hk2 : ι (Ideal.Quotient.mk _ (MvPowerSeries.X 2)) =
          Ideal.Quotient.mk _ (Polynomial.C (PowerSeries.C b)) := pinchModelEquiv_mk_X_two ℂ 0
      refine Ideal.mem_span_pair.mpr ⟨ι.symm (Ideal.Quotient.mk _ (Polynomial.C a₁)),
        ι.symm (Ideal.Quotient.mk _ (Polynomial.C a₀)), ?_⟩
      show _ = e p
      rw [hep]
      apply ι.injective
      rw [map_add, map_mul, map_mul, hk0, hk2, ι.apply_symm_apply, ι.apply_symm_apply,
        ι.apply_symm_apply]
      simp only [r', map_mul, Polynomial.C_mul]
      ring
  rw [hP]
  have hpr : (Ideal.span {(PowerSeries.C b : B⟦X⟧)}).IsPrime :=
    (Ideal.span_singleton_prime (prime_C_X_zero).ne_zero).mpr prime_C_X_zero
  exact Ideal.comap_isPrime ψ _

end PinchRadical

/-! ### Abstract pieces of the crossing computation -/

private theorem exists_hom_integralClosure {E E₁ : Type} [CommRing E] [CommRing E₁] [IsDomain E₁]
    [IsIntegrallyClosed E₁] (ρ : E →+* E₁) (hρ : ∀ s ∈ nonZeroDivisors E, ρ s ≠ 0) :
    ∃ (ρt : FractionRing E →+* FractionRing E₁) (Ψ : integralClosure E (FractionRing E) →+* E₁),
      (∀ r, ρt (algebraMap E _ r) = algebraMap E₁ _ (ρ r)) ∧
      ∀ n, algebraMap E₁ (FractionRing E₁) (Ψ n) = ρt n := by
  have hg : ∀ y : nonZeroDivisors E, IsUnit ((algebraMap E₁ (FractionRing E₁)).comp ρ y) := by
    intro y
    refine IsUnit.mk0 _ ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective E₁ _)).2 (hρ y y.2)
  let ρt : FractionRing E →+* FractionRing E₁ :=
    IsLocalization.lift (M := nonZeroDivisors E) hg
  have hρt : ∀ r, ρt (algebraMap E _ r) = algebraMap E₁ _ (ρ r) := fun r =>
    IsLocalization.lift_eq hg r
  have hint : ∀ n : integralClosure E (FractionRing E),
      ∃ y : E₁, algebraMap E₁ (FractionRing E₁) y = ρt n := by
    intro n
    obtain ⟨p, hp, hpn⟩ := n.2
    have : IsIntegral E₁ (ρt n) := by
      refine ⟨p.map ρ, hp.map _, ?_⟩
      have h0 := congrArg ρt hpn
      rw [map_zero, Polynomial.hom_eval₂] at h0
      have hc : (algebraMap E₁ (FractionRing E₁)).comp ρ =
          ρt.comp (algebraMap E (FractionRing E)) := RingHom.ext fun r => (hρt r).symm
      rw [Polynomial.eval₂_map, hc]
      exact h0
    exact IsIntegrallyClosed.algebraMap_eq_of_integral this
  choose y hy using hint
  have hinj := IsFractionRing.injective E₁ (FractionRing E₁)
  let Ψ : integralClosure E (FractionRing E) →+* E₁ :=
    { toFun := y
      map_one' := hinj (by rw [hy, map_one]; simp)
      map_mul' := fun a b => hinj (by rw [hy, map_mul, hy, hy]; simp)
      map_zero' := hinj (by rw [hy, map_zero]; simp)
      map_add' := fun a b => hinj (by rw [hy, map_add, hy, hy]; simp) }
  exact ⟨ρt, Ψ, hρt, hy⟩

private theorem fractionRing_joint_injective {E E₁ E₂ : Type} [CommRing E] [CommRing E₁]
    [CommRing E₂] (ρ₁ : E →+* E₁) (ρ₂ : E →+* E₂)
    (ρt₁ : FractionRing E →+* FractionRing E₁) (ρt₂ : FractionRing E →+* FractionRing E₂)
    (h₁ : ∀ r, ρt₁ (algebraMap E _ r) = algebraMap E₁ _ (ρ₁ r))
    (h₂ : ∀ r, ρt₂ (algebraMap E _ r) = algebraMap E₂ _ (ρ₂ r))
    (hinj₁ : Function.Injective (algebraMap E₁ (FractionRing E₁)))
    (hinj₂ : Function.Injective (algebraMap E₂ (FractionRing E₂)))
    (hjoint : ∀ r, ρ₁ r = 0 → ρ₂ r = 0 → r = 0)
    (w : FractionRing E) (hw₁ : ρt₁ w = 0) (hw₂ : ρt₂ w = 0) : w = 0 := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors E) w
  have hspec := IsLocalization.mk'_spec (FractionRing E) r s
  have e₁ : algebraMap E₁ (FractionRing E₁) (ρ₁ r) = 0 := by
    rw [← h₁, ← hspec, map_mul, hw₁, zero_mul]
  have e₂ : algebraMap E₂ (FractionRing E₂) (ρ₂ r) = 0 := by
    rw [← h₂, ← hspec, map_mul, hw₂, zero_mul]
  have hr : r = 0 := hjoint r (hinj₁ (by rw [e₁, map_zero])) (hinj₂ (by rw [e₂, map_zero]))
  have : IsLocalization.mk' (FractionRing E) r s * algebraMap E (FractionRing E) s = 0 := by
    rw [hspec, hr, map_zero]
  exact (IsLocalization.map_units (FractionRing E) s).mul_left_eq_zero.mp this

/-- Abstract form of the crossing computation. -/
private theorem radical_mem_range_of_two_quotients {E N E₁ E₂ : Type} [CommRing E] [CommRing N]
    [Algebra E N] [CommRing E₁] [CommRing E₂] [IsDomain E₁] [IsDomain E₂]
    (ρ₁ : E →+* E₁) (ρ₂ : E →+* E₂) (hρ₁ : Function.Surjective ρ₁)
    (hρ₂ : Function.Surjective ρ₂) (Ψ₁ : N →+* E₁) (Ψ₂ : N →+* E₂)
    (hΨ₁ : ∀ r, Ψ₁ (algebraMap E N r) = ρ₁ r) (hΨ₂ : ∀ r, Ψ₂ (algebraMap E N r) = ρ₂ r)
    (hjoint : ∀ n, Ψ₁ n = 0 → Ψ₂ n = 0 → n = 0)
    (x₀ x₁ : E) (h₀ : ρ₁ x₀ = 0) (h₁ : ρ₂ x₁ = 0) (p₁ : Prime (ρ₁ x₁)) (p₂ : Prime (ρ₂ x₀))
    (z : N) (hz : z ∈ (Ideal.map (algebraMap E N) (Ideal.span {x₀, x₁})).radical) :
    z ∈ Set.range (algebraMap E N) := by
  obtain ⟨m, hm⟩ := hz
  -- images of the ideal
  have h1 : Ψ₁ z ^ m ∈ Ideal.span {ρ₁ x₁} := by
    have : Ideal.map (algebraMap E N) (Ideal.span {x₀, x₁}) ≤
        Ideal.comap Ψ₁ (Ideal.span {ρ₁ x₁}) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
      intro p hp
      rcases hp with rfl | rfl
      · simp [hΨ₁, h₀]
      · simp [hΨ₁, Ideal.mem_span_singleton_self]
    have := this hm
    rwa [Ideal.mem_comap, map_pow] at this
  have h2 : Ψ₂ z ^ m ∈ Ideal.span {ρ₂ x₀} := by
    have : Ideal.map (algebraMap E N) (Ideal.span {x₀, x₁}) ≤
        Ideal.comap Ψ₂ (Ideal.span {ρ₂ x₀}) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
      intro p hp
      rcases hp with rfl | rfl
      · simp [hΨ₂, Ideal.mem_span_singleton_self]
      · simp [hΨ₂, h₁]
    have := this hm
    rwa [Ideal.mem_comap, map_pow] at this
  obtain ⟨c₁, hc₁⟩ := p₁.dvd_of_dvd_pow (Ideal.mem_span_singleton.mp h1)
  obtain ⟨c₂, hc₂⟩ := p₂.dvd_of_dvd_pow (Ideal.mem_span_singleton.mp h2)
  obtain ⟨t₁, rfl⟩ := hρ₁ c₁
  obtain ⟨t₂, rfl⟩ := hρ₂ c₂
  refine ⟨x₁ * t₁ + x₀ * t₂, ?_⟩
  symm
  rw [← sub_eq_zero]
  apply hjoint
  · rw [map_sub, hΨ₁, hc₁]; simp [h₀]
  · rw [map_sub, hΨ₂, hc₂]; simp [h₁]

section CrossingRadical

open PowerSeries

private theorem ne_zero_of_mem_nonZeroDivisors_of_ker {E E₁ : Type} [CommRing E] [CommRing E₁]
    (ρ : E →+* E₁) (x₀ x₁ : E) (h : x₀ * x₁ = 0) (hx₁ : x₁ ≠ 0)
    (hker : ∀ s, ρ s = 0 → ∃ t, s = x₀ * t) : ∀ s ∈ nonZeroDivisors E, ρ s ≠ 0 := by
  intro s hs hρs
  obtain ⟨t, rfl⟩ := hker s hρs
  apply hx₁
  refine (mem_nonZeroDivisors_iff.mp hs).1 x₁ ?_
  rw [mul_assoc, mul_comm t, ← mul_assoc, h, zero_mul]

private theorem crossing_radical_mem_range (E : Type) [CommRing E]
    (e : E ≃+* (MvPowerSeries (Fin 3) ℂ ⧸
      Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ)}))
    (z : integralClosure E (FractionRing E))
    (hz : z ∈ (Ideal.map (algebraMap E (integralClosure E (FractionRing E)))
      (Ideal.comap e.toRingHom (Ideal.span {Ideal.Quotient.mk _ (MvPowerSeries.X 0),
        Ideal.Quotient.mk _ (MvPowerSeries.X 1)}))).radical) :
    z ∈ Set.range (algebraMap E (integralClosure E (FractionRing E))) := by
  set R := MvPowerSeries (Fin 3) ℂ with hR
  have : IsRegularLocalRing (MvPowerSeries (Fin 2) ℂ) := MvPowerSeries.isRegularLocalRing ℂ 2
  have : IsDomain (MvPowerSeries (Fin 2) ℂ) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (MvPowerSeries (Fin 2) ℂ) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have : IsRegularLocalRing R := MvPowerSeries.isRegularLocalRing ℂ 3
  have : IsDomain R := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid R := IsRegularLocalRing.uniqueFactorizationMonoid _
  let h : R := MvPowerSeries.X 0 * MvPowerSeries.X 1
  let σ := MvPowerSeries.renameEquiv ℂ (Equiv.swap (0 : Fin 3) 1)
  have hs0 : σ (MvPowerSeries.X 0) = MvPowerSeries.X 1 := by
    simp [σ, MvPowerSeries.renameEquiv, MvPowerSeries.rename_X]
  have hs1 : σ (MvPowerSeries.X 1) = MvPowerSeries.X 0 := by
    simp [σ, MvPowerSeries.renameEquiv, MvPowerSeries.rename_X]
  let swapR : R →+* R := σ.toRingEquiv.toRingHom
  let r₁ : R →+* MvPowerSeries (Fin 2) ℂ := restrictZero ℂ 2
  let r₂ : R →+* MvPowerSeries (Fin 2) ℂ := (restrictZero ℂ 2).comp swapR
  have hr₁h : r₁ h = 0 := by
    show restrictZero ℂ 2 (MvPowerSeries.X 0 * MvPowerSeries.X 1) = 0
    rw [map_mul, restrictZero_X_zero, zero_mul]
  have hswapX0 : swapR (MvPowerSeries.X 0) = MvPowerSeries.X 1 := hs0
  have hswapX1 : swapR (MvPowerSeries.X 1) = MvPowerSeries.X 0 := hs1
  have hr₂h : r₂ h = 0 := by
    show restrictZero ℂ 2 (swapR (MvPowerSeries.X 0 * MvPowerSeries.X 1)) = 0
    rw [map_mul, hswapX0, hswapX1, map_mul, restrictZero_X_zero, mul_zero]
  let Q := R ⧸ Ideal.span {h}
  have hker₁ : ∀ a ∈ Ideal.span {h}, r₁ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hr₁h, mul_zero]
  have hker₂ : ∀ a ∈ Ideal.span {h}, r₂ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hr₂h, mul_zero]
  let ρ₁ : E →+* MvPowerSeries (Fin 2) ℂ :=
    (Ideal.Quotient.lift (Ideal.span {h}) r₁ hker₁).comp e.toRingHom
  let ρ₂ : E →+* MvPowerSeries (Fin 2) ℂ :=
    (Ideal.Quotient.lift (Ideal.span {h}) r₂ hker₂).comp e.toRingHom
  let x₀ : E := e.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 0))
  let x₁ : E := e.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 1))
  have hρ₁ : ∀ f : R, ρ₁ (e.symm (Ideal.Quotient.mk _ f)) = r₁ f := by
    intro f
    show Ideal.Quotient.lift (Ideal.span {h}) r₁ hker₁ (e (e.symm _)) = _
    rw [e.apply_symm_apply, Ideal.Quotient.lift_mk]
  have hρ₂ : ∀ f : R, ρ₂ (e.symm (Ideal.Quotient.mk _ f)) = r₂ f := by
    intro f
    show Ideal.Quotient.lift (Ideal.span {h}) r₂ hker₂ (e (e.symm _)) = _
    rw [e.apply_symm_apply, Ideal.Quotient.lift_mk]
  have hr₁X1 : r₁ (MvPowerSeries.X 1) = MvPowerSeries.X 0 := by
    have h1 : MvPowerSeries.finSuccEquiv ℂ 2 (MvPowerSeries.X 1) =
        PowerSeries.C (MvPowerSeries.X 0) := MvPowerSeries.finSuccEquiv_X_succ (j := 0)
    show PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv ℂ 2 (MvPowerSeries.X 1)) = _
    rw [h1, PowerSeries.constantCoeff_C]
  have hr₂X0 : r₂ (MvPowerSeries.X 0) = MvPowerSeries.X 0 := by
    show restrictZero ℂ 2 (swapR (MvPowerSeries.X 0)) = _
    rw [hswapX0]; exact hr₁X1
  have hr₂X1 : r₂ (MvPowerSeries.X 1) = 0 := by
    show restrictZero ℂ 2 (swapR (MvPowerSeries.X 1)) = _
    rw [hswapX1, restrictZero_X_zero]
  -- surjectivity
  have hsurj₁ : Function.Surjective ρ₁ := fun g =>
    ⟨e.symm (Ideal.Quotient.mk _ (inclZero ℂ 2 g)), by rw [hρ₁]; exact restrictZero_inclZero g⟩
  have hsurj₂ : Function.Surjective ρ₂ := fun g =>
    ⟨e.symm (Ideal.Quotient.mk _ (σ.symm (inclZero ℂ 2 g))), by
      rw [hρ₂]
      show restrictZero ℂ 2 (σ (σ.symm (inclZero ℂ 2 g))) = g
      rw [σ.apply_symm_apply]; exact restrictZero_inclZero g⟩
  -- kernels
  have hdvd₀ : ∀ f : R, (MvPowerSeries.X 0 : R) ∣ f ↔ r₁ f = 0 := fun f => X_zero_dvd_iff f
  have hdvd₁ : ∀ f : R, (MvPowerSeries.X 1 : R) ∣ f ↔ r₂ f = 0 := by
    intro f
    have : (MvPowerSeries.X 1 : R) ∣ f ↔ (MvPowerSeries.X 0 : R) ∣ σ f := by
      constructor
      · rintro ⟨g, rfl⟩; exact ⟨σ g, by rw [map_mul, hs1]⟩
      · rintro ⟨g, hg⟩
        refine ⟨σ.symm g, ?_⟩
        apply σ.injective
        rw [map_mul, hs1, AlgEquiv.apply_symm_apply, hg]
    rw [this, hdvd₀]; rfl
  have hker₁' : ∀ s, ρ₁ s = 0 → ∃ t, s = x₀ * t := by
    intro s hs
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e s)
    have hs' : s = e.symm (Ideal.Quotient.mk _ f) := by rw [hf, e.symm_apply_apply]
    rw [hs', hρ₁] at hs
    obtain ⟨g, rfl⟩ := (hdvd₀ f).mpr hs
    exact ⟨e.symm (Ideal.Quotient.mk _ g), by rw [hs', map_mul, map_mul]⟩
  have hker₂' : ∀ s, ρ₂ s = 0 → ∃ t, s = x₁ * t := by
    intro s hs
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e s)
    have hs' : s = e.symm (Ideal.Quotient.mk _ f) := by rw [hf, e.symm_apply_apply]
    rw [hs', hρ₂] at hs
    obtain ⟨g, rfl⟩ := (hdvd₁ f).mpr hs
    exact ⟨e.symm (Ideal.Quotient.mk _ g), by rw [hs', map_mul, map_mul]⟩
  have hx₀₁ : x₀ * x₁ = 0 := by
    show e.symm _ * e.symm _ = 0
    rw [← map_mul, ← map_mul]
    have : Ideal.Quotient.mk (Ideal.span {h}) (MvPowerSeries.X 0 * MvPowerSeries.X 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self h)
    rw [this, map_zero]
  have hX0ne : (MvPowerSeries.X 0 : R) ≠ 0 := (prime_X (n := 2) 0).ne_zero
  have hX1ne : (MvPowerSeries.X 1 : R) ≠ 0 := (prime_X (n := 2) 1).ne_zero
  have hx₀ne : x₀ ≠ 0 := by
    intro h0
    have h1 : Ideal.Quotient.mk (Ideal.span {h}) (MvPowerSeries.X 0) = 0 := by
      have : e x₀ = 0 := by rw [h0, map_zero]
      rwa [show e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0) from e.apply_symm_apply _] at this
    obtain ⟨c, hc⟩ := Ideal.Quotient.eq_zero_iff_dvd _ _ |>.mp h1
    have : (MvPowerSeries.X 0 : R) * 1 = MvPowerSeries.X 0 * (MvPowerSeries.X 1 * c) := by
      rw [mul_one]; conv_lhs => rw [hc]
      ring
    exact (prime_X (n := 2) 1).not_isUnit (isUnit_iff_exists_inv.mpr ⟨c,
      (mul_left_cancel₀ hX0ne this).symm⟩)
  have hx₁ne : x₁ ≠ 0 := by
    intro h0
    have h1 : Ideal.Quotient.mk (Ideal.span {h}) (MvPowerSeries.X 1) = 0 := by
      have : e x₁ = 0 := by rw [h0, map_zero]
      rwa [show e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1) from e.apply_symm_apply _] at this
    obtain ⟨c, hc⟩ := Ideal.Quotient.eq_zero_iff_dvd _ _ |>.mp h1
    have : (MvPowerSeries.X 1 : R) * 1 = MvPowerSeries.X 1 * (MvPowerSeries.X 0 * c) := by
      rw [mul_one]; conv_lhs => rw [hc]
      ring
    exact (prime_X (n := 2) 0).not_isUnit (isUnit_iff_exists_inv.mpr ⟨c,
      (mul_left_cancel₀ hX1ne this).symm⟩)
  have hnz₁ := ne_zero_of_mem_nonZeroDivisors_of_ker ρ₁ x₀ x₁ hx₀₁ hx₁ne hker₁'
  have hnz₂ := ne_zero_of_mem_nonZeroDivisors_of_ker ρ₂ x₁ x₀ (by rw [mul_comm]; exact hx₀₁)
    hx₀ne hker₂'
  have hp₁ : Prime (ρ₁ x₁) := by
    show Prime (ρ₁ (e.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 1))))
    rw [hρ₁, hr₁X1]; exact prime_X (n := 1) 0
  have hp₂ : Prime (ρ₂ x₀) := by
    show Prime (ρ₂ (e.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 0))))
    rw [hρ₂, hr₂X0]; exact prime_X (n := 1) 0
  have hrel : IsRelPrime (MvPowerSeries.X 0 : R) (MvPowerSeries.X 1) := by
    refine ((prime_X (n := 2) 0).irreducible.isRelPrime_iff_not_dvd).mpr ?_
    intro hd
    have := (hdvd₀ _).mp hd
    rw [hr₁X1] at this
    exact (prime_X (n := 1) 0).ne_zero this
  have hjointE : ∀ r : E, ρ₁ r = 0 → ρ₂ r = 0 → r = 0 := by
    intro r h1 h2
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e r)
    have hr' : r = e.symm (Ideal.Quotient.mk _ f) := by rw [hf, e.symm_apply_apply]
    rw [hr', hρ₁] at h1
    rw [hr', hρ₂] at h2
    have := hrel.mul_dvd ((hdvd₀ f).mpr h1) ((hdvd₁ f).mpr h2)
    rw [hr', (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr this, map_zero]
  obtain ⟨ρt₁, Ψ₁, hρt₁, hΨ₁y⟩ := exists_hom_integralClosure ρ₁ hnz₁
  obtain ⟨ρt₂, Ψ₂, hρt₂, hΨ₂y⟩ := exists_hom_integralClosure ρ₂ hnz₂
  have hinj₁ := IsFractionRing.injective (MvPowerSeries (Fin 2) ℂ)
    (FractionRing (MvPowerSeries (Fin 2) ℂ))
  have hΨ₁ : ∀ r, Ψ₁ (algebraMap E (integralClosure E (FractionRing E)) r) = ρ₁ r := by
    intro r
    apply hinj₁
    rw [hΨ₁y]
    exact hρt₁ r
  have hΨ₂ : ∀ r, Ψ₂ (algebraMap E (integralClosure E (FractionRing E)) r) = ρ₂ r := by
    intro r
    apply hinj₁
    rw [hΨ₂y]
    exact hρt₂ r
  have hjointN : ∀ n : integralClosure E (FractionRing E), Ψ₁ n = 0 → Ψ₂ n = 0 → n = 0 := by
    intro n h1 h2
    exact Subtype.ext <| fractionRing_joint_injective ρ₁ ρ₂ ρt₁ ρt₂ hρt₁ hρt₂ hinj₁ hinj₁ hjointE
      (n : FractionRing E) (by rw [← hΨ₁y n, h1, map_zero]) (by rw [← hΨ₂y n, h2, map_zero])
  have hP : Ideal.comap e.toRingHom
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {h}) (MvPowerSeries.X 0),
      Ideal.Quotient.mk (Ideal.span {h}) (MvPowerSeries.X 1)}) = Ideal.span {x₀, x₁} := by
    ext p
    rw [Ideal.mem_comap, Ideal.mem_span_pair, Ideal.mem_span_pair]
    constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨e.symm a, e.symm b, e.injective ?_⟩
      rw [map_add, map_mul, map_mul]
      simpa [x₀, x₁] using hab
    · rintro ⟨a, b, hab⟩
      refine ⟨e a, e b, ?_⟩
      have := congrArg e hab
      rw [map_add, map_mul, map_mul] at this
      simpa [x₀, x₁] using this
  rw [hP] at hz
  exact radical_mem_range_of_two_quotients ρ₁ ρ₂ hsurj₁ hsurj₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ hjointN x₀ x₁
    (by
      show ρ₁ (e.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 0))) = 0
      rw [hρ₁]; exact restrictZero_X_zero)
    (by
      show ρ₂ (e.symm (Ideal.Quotient.mk _ (MvPowerSeries.X 1))) = 0
      rw [hρ₂]; exact hr₂X1) hp₁ hp₂ z hz

private theorem crossing_isPrime (E : Type) [CommRing E]
    (e : E ≃+* (MvPowerSeries (Fin 3) ℂ ⧸
      Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ)})) :
    (Ideal.comap e.toRingHom (Ideal.span {Ideal.Quotient.mk _ (MvPowerSeries.X 0),
        Ideal.Quotient.mk _ (MvPowerSeries.X 1)})).IsPrime := by
  set R := MvPowerSeries (Fin 3) ℂ with hR
  have : IsRegularLocalRing (MvPowerSeries (Fin 2) ℂ) := MvPowerSeries.isRegularLocalRing ℂ 2
  have : IsDomain (MvPowerSeries (Fin 2) ℂ) := IsRegularLocalRing.isDomain _
  let h : R := MvPowerSeries.X 0 * MvPowerSeries.X 1
  let r₁ : R →+* MvPowerSeries (Fin 2) ℂ := restrictZero ℂ 2
  have hr₁h : r₁ h = 0 := by
    show restrictZero ℂ 2 (MvPowerSeries.X 0 * MvPowerSeries.X 1) = 0
    rw [map_mul, restrictZero_X_zero, zero_mul]
  have hker₁ : ∀ a ∈ Ideal.span {h}, r₁ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hr₁h, mul_zero]
  let ρ₁ : E →+* MvPowerSeries (Fin 2) ℂ :=
    (Ideal.Quotient.lift (Ideal.span {h}) r₁ hker₁).comp e.toRingHom
  have hr₁X1 : r₁ (MvPowerSeries.X 1) = MvPowerSeries.X 0 := by
    have h1 : MvPowerSeries.finSuccEquiv ℂ 2 (MvPowerSeries.X 1) =
        PowerSeries.C (MvPowerSeries.X 0) := MvPowerSeries.finSuccEquiv_X_succ (j := 0)
    show PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv ℂ 2 (MvPowerSeries.X 1)) = _
    rw [h1, PowerSeries.constantCoeff_C]
  have hρ₁ : ∀ f : R, ρ₁ (e.symm (Ideal.Quotient.mk _ f)) = r₁ f := by
    intro f
    show Ideal.Quotient.lift (Ideal.span {h}) r₁ hker₁ (e (e.symm _)) = _
    rw [e.apply_symm_apply, Ideal.Quotient.lift_mk]
  have hP : Ideal.comap e.toRingHom (Ideal.span {(Ideal.Quotient.mk (Ideal.span {h})
      (MvPowerSeries.X 0)), (Ideal.Quotient.mk (Ideal.span {h}) (MvPowerSeries.X 1))}) =
      Ideal.comap ρ₁ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ)}) := by
    ext s
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_span_singleton]
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e s)
    have hs' : s = e.symm (Ideal.Quotient.mk _ f) := by rw [hf, e.symm_apply_apply]
    have hes : e.toRingHom s = Ideal.Quotient.mk _ f := hf.symm
    rw [hes, hs', hρ₁]
    constructor
    · intro hmem
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
      obtain ⟨fa, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨fb, rfl⟩ := Ideal.Quotient.mk_surjective b
      have : Ideal.Quotient.mk (Ideal.span {h}) (fa * MvPowerSeries.X 0 + fb * MvPowerSeries.X 1)
          = Ideal.Quotient.mk (Ideal.span {h}) f := by rw [map_add, map_mul, map_mul]; exact hab
      have hdiff := Ideal.Quotient.eq.mp this
      have hr := hker₁ _ hdiff
      have hX0z : r₁ (MvPowerSeries.X 0) = 0 := restrictZero_X_zero
      simp only [map_sub, map_add, map_mul, hX0z, hr₁X1, mul_zero, zero_add] at hr
      exact ⟨r₁ fb, by rw [mul_comm]; exact (sub_eq_zero.mp hr).symm⟩
    · rintro ⟨c, hc⟩
      obtain ⟨g, rfl⟩ : ∃ g, r₁ g = c := ⟨inclZero ℂ 2 c, restrictZero_inclZero c⟩
      have h0 : r₁ (f - MvPowerSeries.X 1 * g) = 0 := by
        rw [map_sub, map_mul, hr₁X1, hc, sub_self]
      obtain ⟨g', hg'⟩ := (X_zero_dvd_iff _).mpr h0
      refine Ideal.mem_span_pair.mpr ⟨Ideal.Quotient.mk _ g', Ideal.Quotient.mk _ g, ?_⟩
      have : f = MvPowerSeries.X 0 * g' + MvPowerSeries.X 1 * g := by
        rw [← hg']; ring
      rw [this, map_add, map_mul, map_mul]; ring
  rw [hP]
  have hpr : (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ)}).IsPrime :=
    (Ideal.span_singleton_prime (prime_X (n := 1) 0).ne_zero).mpr (prime_X (n := 1) 0)
  exact Ideal.comap_isPrime ρ₁ _

end CrossingRadical

/-! ### The semismooth local models (steps 5 and 6) -/

/-- `P` is the ideal of the singular locus of the standard model of a double normal crossing point
(`ℂ⟦x₀,x₁,x₂⟧ ⧸ (x₀x₁)`, `P = (x₀, x₁)`) or of a pinch point (`ℂ⟦x₀,x₁,x₂⟧ ⧸ (x₀² - x₁x₂²)`,
`P = (x₀, x₂)`), transported along a ring isomorphism. -/
private def IsModelSingularIdeal (E : Type) [CommRing E] (P : Ideal E) : Prop :=
  (∃ e : E ≃+* (MvPowerSeries (Fin 3) ℂ ⧸
        Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ)}),
      P = Ideal.comap e.toRingHom (Ideal.span {Ideal.Quotient.mk _ (MvPowerSeries.X 0),
        Ideal.Quotient.mk _ (MvPowerSeries.X 1)})) ∨
  (∃ e : E ≃+* (MvPowerSeries (Fin 3) ℂ ⧸
        Ideal.span {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
          MvPowerSeries (Fin 3) ℂ)}),
      P = Ideal.comap e.toRingHom (Ideal.span {Ideal.Quotient.mk _ (MvPowerSeries.X 0),
        Ideal.Quotient.mk _ (MvPowerSeries.X 2)}))

/-- Step 6: in the integral closure of a model ring in its total ring of fractions, an element of
the radical of the extended singular ideal comes from the model ring. -/
private theorem model_radical_mem_range (E : Type) [CommRing E] (P : Ideal E)
    (hP : IsModelSingularIdeal E P)
    (z : integralClosure E (FractionRing E))
    (hz : z ∈ (Ideal.map (algebraMap E (integralClosure E (FractionRing E))) P).radical) :
    z ∈ Set.range (algebraMap E (integralClosure E (FractionRing E))) := by
  rcases hP with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · exact crossing_radical_mem_range E e z hz
  · exact pinch_radical_mem_range E e z hz

/-- The singular ideal of a model is prime (the quotient is a power series ring in one
variable). -/
private theorem isPrime_of_isModelSingularIdeal (E : Type) [CommRing E] (P : Ideal E)
    (hP : IsModelSingularIdeal E P) : P.IsPrime := by
  rcases hP with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · exact crossing_isPrime E e
  · exact pinch_isPrime E e

/-- Step 5: the prime of `A` under the singular ideal of the model of `Â` is not regular
(regularity ascends along the regular map `A → Â`, and the model is not regular there). -/
private theorem not_isRegularLocalRing_comap_of_isModelSingularIdeal (A : Type) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (hG : IsGRing A)
    (P : Ideal (AdicCompletion (maximalIdeal A) A)) [P.IsPrime]
    (hP : IsModelSingularIdeal _ P) :
    ¬ IsRegularLocalRing
      (Localization.AtPrime (P.comap (algebraMap A (AdicCompletion (maximalIdeal A) A)))) := by
  intro hreg
  have hPreg : IsRegularLocalRing (Localization.AtPrime P) :=
    (isRegularLocalRing_localization_adicCompletion_iff hG P).mpr hreg
  rcases hP with ⟨e, hPe⟩ | ⟨e, hPe⟩
  · set q : Ideal (MvPowerSeries (Fin 3) ℂ ⧸ Ideal.span {(MvPowerSeries.X 0 *
      MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ)}) := Ideal.span {(Ideal.Quotient.mk _
        (MvPowerSeries.X 0)), (Ideal.Quotient.mk _ (MvPowerSeries.X 1))}
    have hqprime : q.IsPrime := by
      rw [show q = Ideal.comap e.symm.toRingHom P by
        rw [hPe, Ideal.comap_comap]; ext; simp]
      exact Ideal.comap_isPrime _ _
    have hreg' : IsRegularLocalRing (Localization.AtPrime q) :=
      (isRegularLocalRing_localization_comap_iff e q).mp (hPe ▸ hPreg)
    have := (SingLoc.Pub.isRegularLocalRing_localization_dnc_iff (k := ℂ) (m := 1) q).mp hreg'
    exact this ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩
  · set q : Ideal (MvPowerSeries (Fin 3) ℂ ⧸ Ideal.span {(MvPowerSeries.X 0 ^ 2 -
      MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 : MvPowerSeries (Fin 3) ℂ)}) :=
        Ideal.span {Ideal.Quotient.mk _ (MvPowerSeries.X 0),
          Ideal.Quotient.mk _ (MvPowerSeries.X 2)}
    have hqprime : q.IsPrime := by
      rw [show q = Ideal.comap e.symm.toRingHom P by
        rw [hPe, Ideal.comap_comap]; ext; simp]
      exact Ideal.comap_isPrime _ _
    have hreg' : IsRegularLocalRing (Localization.AtPrime q) :=
      (isRegularLocalRing_localization_comap_iff e q).mp (hPe ▸ hPreg)
    have := (SingLoc.Pub.isRegularLocalRing_localization_pinch_iff (k := ℂ) (m := 0) q).mp hreg'
    exact this ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩

/-- The ideal of functions vanishing on the non-regular locus of `Spec A`. -/
private def nonRegularIdeal (A : Type) [CommRing A] : Ideal A :=
  sInf {q : Ideal A | ∃ _ : q.IsPrime, ¬ IsRegularLocalRing (Localization.AtPrime q)}

/-- Steps 4 to 6 combined: an element `j` of the normalization stalk `A'` in the radical of
`nonRegularIdeal A · A'` comes from `A`. -/
private theorem mem_range_of_model (A A' : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hG : IsGRing A) [CommRing A'] [Algebra A A']
    (g : A' ⊗[A] AdicCompletion (maximalIdeal A) A →+*
      FractionRing (AdicCompletion (maximalIdeal A) A))
    (hginj : Function.Injective g)
    (hgrange : g.range = (integralClosure (AdicCompletion (maximalIdeal A) A)
      (FractionRing (AdicCompletion (maximalIdeal A) A))).toSubring)
    (hgy : ∀ y : AdicCompletion (maximalIdeal A) A,
      g (1 ⊗ₜ y) = algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) y)
    (P : Ideal (AdicCompletion (maximalIdeal A) A)) (hP : IsModelSingularIdeal _ P)
    (j : A') (hj : j ∈ (Ideal.map (algebraMap A A') (nonRegularIdeal A)).radical) :
    j ∈ Set.range (algebraMap A A') := by
  have hprime : P.IsPrime := isPrime_of_isModelSingularIdeal _ P hP
  have hI : nonRegularIdeal A ≤ P.comap (algebraMap A (AdicCompletion (maximalIdeal A) A)) :=
    sInf_le ⟨inferInstance, not_isRegularLocalRing_comap_of_isModelSingularIdeal A hG P hP⟩
  have : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
    faithfullyFlat_adicCompletion A
  set Ac := AdicCompletion (maximalIdeal A) A
  set K := FractionRing Ac
  set N := integralClosure Ac K
  have hmem : ∀ w : A', g (w ⊗ₜ 1) ∈ N := by
    intro w
    have : g (w ⊗ₜ 1) ∈ g.range := ⟨_, rfl⟩
    rw [hgrange] at this
    exact this
  let φ : A' →+* N :=
    (g.comp Algebra.TensorProduct.includeLeftRingHom).codRestrict N.toSubring hmem
  have hφ : ∀ w, (φ w : K) = g (w ⊗ₜ 1) := fun w => rfl
  have hφA : ∀ a : A, φ (algebraMap A A' a) = algebraMap Ac N (algebraMap A Ac a) := by
    intro a
    apply Subtype.ext
    rw [hφ]
    have h1 : (algebraMap A A' a) ⊗ₜ[A] (1 : Ac) = (1 : A') ⊗ₜ[A] (algebraMap A Ac a) := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
    rw [h1, hgy]
    rfl
  -- the image of `j` lies in the radical of `P N`
  obtain ⟨n, hn⟩ := hj
  have hz : φ j ∈ (Ideal.map (algebraMap Ac N) P).radical := by
    refine ⟨n, ?_⟩
    rw [← map_pow]
    have : φ (j ^ n) ∈ Ideal.map φ (Ideal.map (algebraMap A A') (nonRegularIdeal A)) :=
      Ideal.mem_map_of_mem φ hn
    refine (?_ : Ideal.map φ (Ideal.map (algebraMap A A') (nonRegularIdeal A)) ≤ _) this
    rw [Ideal.map_map]
    have e : φ.comp (algebraMap A A') = (algebraMap Ac N).comp (algebraMap A Ac) :=
      RingHom.ext hφA
    rw [e, ← Ideal.map_map]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr hI)
  obtain ⟨y, hy⟩ := model_radical_mem_range Ac P hP (φ j) hz
  refine mem_range_of_tmul_eq j ⟨y, hginj ?_⟩
  have : g (j ⊗ₜ 1) = algebraMap Ac K y := by
    have := congrArg Subtype.val hy
    rw [← hφ]; exact this.symm
  rw [this, hgy]

/-! ### Stalks to local lifts (step 1) -/

private theorem local_preimage_of_germ_mem_range {S : Scheme.{0}}
    (hX : ∀ U : S.Opens, IsCompact (U : Set S) → (irreducibleComponents U).Finite) (x : S)
    (V : S.Opens) (hxV : x ∈ V)
    (g : Γ(Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX,
      Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ V))
    (h : letI := Scheme.normalizationPushforwardStalkAlgebra S hX x
      (TopCat.Presheaf.germ ((TopCat.Sheaf.pushforward CommRingCat
        (Stacks.AlgebraicGeometry.Normalization.normalization S hX).base).obj
        (Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX).sheaf).presheaf
        V x hxV).hom g ∈
        Set.range (algebraMap (S.presheaf.stalk x) (Scheme.normalizationPushforwardStalk S hX x))) :
    ∃ (U' : S.Opens) (hU' : U' ≤ V), x ∈ U' ∧
      (Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono
          (Stacks.AlgebraicGeometry.Normalization.normalization S hX) hU')).op g ∈
        Set.range ((Stacks.AlgebraicGeometry.Normalization.normalization S hX).app U').hom := by
  let _ := Scheme.normalizationPushforwardStalkAlgebra S hX x
  obtain ⟨a, ha⟩ := h
  obtain ⟨U₁, m₁, f, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.presheaf a
  have hmap : algebraMap (S.presheaf.stalk x) (Scheme.normalizationPushforwardStalk S hX x)
      ((S.presheaf.germ U₁ x m₁).hom f) =
      (TopCat.Presheaf.germ ((TopCat.Sheaf.pushforward CommRingCat
        (Stacks.AlgebraicGeometry.Normalization.normalization S hX).base).obj
        (Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX).sheaf).presheaf
        U₁ x m₁).hom
        ((Stacks.AlgebraicGeometry.Normalization.normalization S hX).app U₁ |>.hom f) := by
    have := TopCat.Presheaf.stalkFunctor_map_germ U₁ x m₁
      (Stacks.AlgebraicGeometry.Normalization.normalization S hX).c
    exact ConcreteCategory.congr_hom this f
  rw [hmap] at ha
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ x m₁ hxV _ _ ha
  refine ⟨W, iV.le, hxW, S.presheaf.map iU.op f, ?_⟩
  exact (app_restrict (Stacks.AlgebraicGeometry.Normalization.normalization S hX) iU f).trans hW

/-! ### The stalk statement (steps 2, 3, 5, 6 assembled) -/

private theorem essFiniteType_stalk_algebra {S : Scheme.{0}} (sX : S ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (x : S) :
    letI := (stalkStructureMap sX x).toAlgebra
    Algebra.EssFiniteType ℂ (S.presheaf.stalk x) := by
  letI := (stalkStructureMap sX x).toAlgebra
  have h := AlgebraicGeometry.essFiniteType_stalkStructureMap sX x
  rw [← RingHom.essFiniteType_algebraMap]
  have e : algebraMap ℂ (S.presheaf.stalk x) = ((sX.stalkMap x).hom.comp
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec (.of ℂ)).presheaf.germ ⊤ (sX.base x) (by simp)).hom) := by
    ext c
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    unfold MMP.Flips.stalkStructureMap
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply]
    rw [Scheme.Hom.germ_stalkMap_apply]
    rfl
  rw [e]; exact h

/-! ### Step 2: sections vanishing on `D^ν` -/

private theorem mem_radical_map_of_vanish {A₀ B : Type*} [CommRing A₀] [CommRing B] [Algebra A₀ B]
    (Z : Set (PrimeSpectrum A₀)) (hZ : IsClosed Z) (j : B)
    (hj : ∀ Q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap A₀ B) Q ∈ Z → j ∈ Q.asIdeal) :
    j ∈ (Ideal.map (algebraMap A₀ B) (PrimeSpectrum.vanishingIdeal Z)).radical := by
  rw [Ideal.radical_eq_sInf]
  refine Ideal.mem_sInf.mpr fun P ⟨hP, hprime⟩ => ?_
  let Q : PrimeSpectrum B := ⟨P, hprime⟩
  apply hj Q
  have : PrimeSpectrum.vanishingIdeal Z ≤ Ideal.comap (algebraMap A₀ B) P :=
    Ideal.map_le_iff_le_comap.mp hP
  have hmem : PrimeSpectrum.comap (algebraMap A₀ B) Q ∈ PrimeSpectrum.zeroLocus
      (PrimeSpectrum.vanishingIdeal Z : Set A₀) := this
  rwa [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq] at hmem

private theorem mem_radical_map_of_square {A₀ B A A' : Type*} [CommRing A₀] [CommRing B]
    [CommRing A] [CommRing A'] (φ₀ : A₀ →+* A) (φ : A₀ →+* B) (ψ : A →+* A') (χ : B →+* A')
    (hsq : χ.comp φ = ψ.comp φ₀) (I₀ : Ideal A₀) (I : Ideal A) (hI : I₀.map φ₀ ≤ I) (j : B)
    (hj : j ∈ (I₀.map φ).radical) : χ j ∈ (I.map ψ).radical := by
  obtain ⟨n, hn⟩ := hj
  refine ⟨n, ?_⟩
  rw [← map_pow]
  have h1 : χ (j ^ n) ∈ Ideal.map χ (I₀.map φ) := Ideal.mem_map_of_mem χ hn
  rw [Ideal.map_map, hsq, ← Ideal.map_map] at h1
  exact Ideal.map_mono hI h1

private theorem mem_prime_of_ker_app {Y S : Scheme.{0}} (ν : Y ⟶ S) (T : Set S) (hT : IsClosed T)
    (W : S.Opens) (hW : IsAffineOpen W) (hU : IsAffineOpen (ν ⁻¹ᵁ W))
    (j : Γ(Y, ν ⁻¹ᵁ W))
    (hj : ((Scheme.IdealSheafData.vanishingIdeal
        (⟨ν.base ⁻¹' T, hT.preimage ν.continuous⟩ : Closeds Y)).subschemeι.app (ν ⁻¹ᵁ W)).hom j = 0)
    (Q : PrimeSpectrum Γ(Y, ν ⁻¹ᵁ W))
    (hQ : hW.fromSpec (PrimeSpectrum.comap (ν.app W).hom Q) ∈ T) : j ∈ Q.asIdeal := by
  let I := Scheme.IdealSheafData.vanishingIdeal
        (⟨ν.base ⁻¹' T, hT.preimage ν.continuous⟩ : Closeds Y)
  have h1 : j ∈ RingHom.ker (I.subschemeι.app (ν ⁻¹ᵁ W)).hom := hj
  have h2 := Scheme.IdealSheafData.ker_subschemeι_app I ⟨ν ⁻¹ᵁ W, hU⟩
  rw [h2, Scheme.IdealSheafData.vanishingIdeal_ideal] at h1
  have h3 := (PrimeSpectrum.mem_vanishingIdeal _ _).mp h1 Q
  apply h3
  change ν.base (hU.fromSpec Q) ∈ T
  have h4 := IsAffineOpen.SpecMap_appLE_fromSpec ν hW hU le_rfl
  have h5 := congrArg (fun f => f.base Q) h4
  have h6 : ν.base (hU.fromSpec.base Q) = hW.fromSpec.base
      ((Spec.map (ν.appLE W (ν ⁻¹ᵁ W) le_rfl)).base Q) := h5.symm
  have e : (Spec.map (ν.appLE W (ν ⁻¹ᵁ W) le_rfl)).base Q =
      PrimeSpectrum.comap (ν.app W).hom Q := by
    rw [Scheme.Hom.appLE_eq_app]; rfl
  rw [e] at h6
  change ν.base (hU.fromSpec.base Q) ∈ T
  rw [h6]
  exact hQ

private theorem isRegularLocalRing_atPrime_comap_iff {A₀ A : Type} [CommRing A₀] [CommRing A]
    [Algebra A₀ A] (M : Submonoid A₀) [IsLocalization M A] (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) ↔
      IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A₀ A))) := by
  let : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap A₀ A)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (T := Localization.AtPrime q) q
  let e := IsLocalization.algEquiv (q.comap (algebraMap A₀ A)).primeCompl
    (Localization.AtPrime (q.comap (algebraMap A₀ A))) (Localization.AtPrime q)
  exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv,
    fun _ => IsRegularLocalRing.of_ringEquiv e.toRingEquiv⟩

private theorem map_germ_vanishingIdeal_le {S : Scheme.{0}} {sX : S ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX]
    (hpts : ∀ x : S, IsClosed ({x} : Set S) →
      x ∈ smoothLocus sX ∨ IsDoubleNormalCrossingPoint sX 2 x ∨ IsPinchPoint sX 2 x)
    (W : S.Opens) (hW : IsAffineOpen W) (x : S) (hxW : x ∈ W) :
    Ideal.map (S.presheaf.germ W x hxW).hom (PrimeSpectrum.vanishingIdeal
      (hW.fromSpec.base ⁻¹' ((smoothLocus sX : Set S)ᶜ))) ≤
        nonRegularIdeal (S.presheaf.stalk x) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap]
  refine Ideal.mem_sInf.mpr ?_
  rintro q ⟨hq, hnreg⟩
  letI : Algebra Γ(S, W) (S.presheaf.stalk x) := (S.presheaf.germ W x hxW).hom.toAlgebra
  haveI : IsLocalization.AtPrime (S.presheaf.stalk x) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hxW⟩
  let p₀ : PrimeSpectrum Γ(S, W) := ⟨q.comap (S.presheaf.germ W x hxW).hom, Ideal.comap_isPrime _ _⟩
  let p₁ : Spec Γ(S, W) := p₀
  have hs : hW.fromSpec.base p₁ ∈ ((smoothLocus sX : Set S)ᶜ) := by
    intro hsm
    have hsW : hW.fromSpec.base p₁ ∈ W := by
      have : hW.fromSpec.base p₁ ∈ Set.range hW.fromSpec.base := ⟨p₁, rfl⟩
      rwa [hW.range_fromSpec] at this
    have hreg_s := (mem_smoothLocus_iff_isRegularLocalRing hpts _).mp hsm
    letI := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨hW.fromSpec.base p₁, hsW⟩
    haveI : IsLocalization.AtPrime (S.presheaf.stalk (hW.fromSpec.base p₁)) p₀.asIdeal :=
      hW.isLocalization_stalk' p₀ hsW
    have e₂ := IsLocalization.algEquiv p₀.asIdeal.primeCompl
      (Localization.AtPrime p₀.asIdeal) (S.presheaf.stalk (hW.fromSpec.base p₁))
    have hreg_p : IsRegularLocalRing (Localization.AtPrime p₀.asIdeal) :=
      IsRegularLocalRing.of_ringEquiv e₂.symm.toRingEquiv
    exact hnreg ((isRegularLocalRing_atPrime_comap_iff (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl
      q).mpr hreg_p)
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha p₀ hs

/-- Step 2: a section vanishing on `D^ν` has, in the normalization stalk at a closed point `x`, a
power in the ideal generated by the functions vanishing on the non-regular locus of
`Spec 𝒪_{S,x}`. -/
private theorem germ_mem_radical_nonRegularIdeal
    {S : Scheme.{0}} {sX : S ⟶ Spec (.of ℂ)} (hS : IsSemismooth sX 2)
    (hX : ∀ U : S.Opens, IsCompact (U : Set S) → (irreducibleComponents U).Finite)
    (V : S.Opens)
    (g : Γ(Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX,
      Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ V))
    (hg : ((Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹'
            (smoothLocus sX : Set S)ᶜ,
          (smoothLocus sX).isOpen.isClosed_compl.preimage
            (Stacks.AlgebraicGeometry.Normalization.normalization S hX).continuous⟩).subschemeι.app
        (Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ V)).hom g = 0)
    (x : S) (hxV : x ∈ V) :
    letI := Scheme.normalizationPushforwardStalkAlgebra S hX x
    (TopCat.Presheaf.germ ((TopCat.Sheaf.pushforward CommRingCat
        (Stacks.AlgebraicGeometry.Normalization.normalization S hX).base).obj
        (Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX).sheaf).presheaf
        V x hxV).hom g ∈
      (Ideal.map (algebraMap (S.presheaf.stalk x) (Scheme.normalizationPushforwardStalk S hX x))
        (nonRegularIdeal (S.presheaf.stalk x))).radical := by
  have hred : IsReduced S := hS.1.2.1
  have : LocallyOfFiniteType sX := hS.1.1.2.1
  let _ := Scheme.normalizationPushforwardStalkAlgebra S hX x
  have : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization S hX) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field ℂ sX) hX
  obtain ⟨W, hWaff, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hxV
  have hW : IsAffineOpen W := hWaff
  have hU : IsAffineOpen (Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ W) :=
    hW.preimage _
  let T : Set S := (smoothLocus sX : Set S)ᶜ
  have hT : IsClosed T := (smoothLocus sX).isOpen.isClosed_compl
  let jB : Γ(Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX,
      Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ W) :=
    (Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono (Stacks.AlgebraicGeometry.Normalization.normalization S hX)
        hWV)).op g
  have hjB : ((Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹' T,
          hT.preimage
            (Stacks.AlgebraicGeometry.Normalization.normalization S hX).continuous⟩).subschemeι.app
        (Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ W)).hom jB = 0 := by
    have := app_restrict (Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹' T,
          hT.preimage
              (Stacks.AlgebraicGeometry.Normalization.normalization S hX).continuous⟩).subschemeι
      (homOfLE (Scheme.Hom.preimage_mono (Stacks.AlgebraicGeometry.Normalization.normalization S hX)
        hWV)) g
    exact this.trans (by rw [hg, map_zero])
  letI : Algebra Γ(S, W) Γ(Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX,
      Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ W) :=
    ((Stacks.AlgebraicGeometry.Normalization.normalization S hX).app W).hom.toAlgebra
  have hrad := mem_radical_map_of_vanish (A₀ := Γ(S, W))
    (hW.fromSpec.base ⁻¹' T) (hT.preimage hW.fromSpec.continuous) jB
    (fun Q hQ => mem_prime_of_ker_app _ T hT W hW hU jB hjB Q hQ)
  let F := ((TopCat.Sheaf.pushforward CommRingCat
    (Stacks.AlgebraicGeometry.Normalization.normalization S hX).base).obj
    (Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX).sheaf).presheaf
  have hsq : ((F.germ W x hxW).hom).comp
      ((Stacks.AlgebraicGeometry.Normalization.normalization S hX).app W).hom =
      (algebraMap (S.presheaf.stalk x) (Scheme.normalizationPushforwardStalk S hX x)).comp
        (S.presheaf.germ W x hxW).hom := by
    refine RingHom.ext fun a => ?_
    have := TopCat.Presheaf.stalkFunctor_map_germ W x hxW
      (Stacks.AlgebraicGeometry.Normalization.normalization S hX).c
    exact (ConcreteCategory.congr_hom this a).symm
  have hI := map_germ_vanishingIdeal_le hS.2 W hW x hxW
  have h2 := mem_radical_map_of_square (S.presheaf.germ W x hxW).hom
    ((Stacks.AlgebraicGeometry.Normalization.normalization S hX).app W).hom
    (algebraMap (S.presheaf.stalk x) (Scheme.normalizationPushforwardStalk S hX x))
    (F.germ W x hxW).hom hsq _ _ hI jB hrad
  have h3 : (F.germ W x hxW).hom jB = (F.germ V x hxV).hom g :=
    TopCat.Presheaf.germ_res_apply F (homOfLE hWV) x hxW g
  rw [← h3]
  exact h2

/-- The germ in the normalization stalk of a section vanishing on `D^ν` comes from `𝒪_{S,x}`. -/
private theorem germ_mem_range
    {S : Scheme.{0}} {sX : S ⟶ Spec (.of ℂ)} (hS : IsSemismooth sX 2)
    (hX : ∀ U : S.Opens, IsCompact (U : Set S) → (irreducibleComponents U).Finite)
    (V : S.Opens)
    (g : Γ(Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX,
      Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ V))
    (hg : ((Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹'
            (smoothLocus sX : Set S)ᶜ,
          (smoothLocus sX).isOpen.isClosed_compl.preimage
            (Stacks.AlgebraicGeometry.Normalization.normalization S hX).continuous⟩).subschemeι.app
        (Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ V)).hom g = 0)
    (x : S) (hxV : x ∈ V) (hxc : IsClosed ({x} : Set S)) :
    letI := Scheme.normalizationPushforwardStalkAlgebra S hX x
    (TopCat.Presheaf.germ ((TopCat.Sheaf.pushforward CommRingCat
        (Stacks.AlgebraicGeometry.Normalization.normalization S hX).base).obj
        (Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX).sheaf).presheaf
        V x hxV).hom g ∈
      Set.range
          (algebraMap (S.presheaf.stalk x) (Scheme.normalizationPushforwardStalk S hX x)) := by
  have hred : IsReduced S := hS.1.2.1
  have : LocallyOfFiniteType sX := hS.1.1.2.1
  letI := Scheme.normalizationPushforwardStalkAlgebra S hX x
  by_cases hsm : x ∈ smoothLocus sX
  · have hreg := (mem_smoothLocus_iff_isRegularLocalRing hS.2 x).mp hsm
    have e0 :=
        Stacks.AlgebraicGeometry.NormalizationQuotient.normalizationStalkAlgEquivIntegralClosureSelf
      S hX x
    exact (surjective_algebraMap_of_isRegularLocalRing hreg e0) _
  · letI := (stalkStructureMap sX x).toAlgebra
    have : Algebra.EssFiniteType ℂ (S.presheaf.stalk x) := essFiniteType_stalk_algebra sX x
    have hexc : IsExcellent (S.presheaf.stalk x) :=
      AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent ℂ
        ((isExcellent_of_standard_classes_and_finiteType.{0, 0}).1 ℂ) sX x
    have : IsNoetherianRing (S.presheaf.stalk x) := hexc.1.1
    have hrad := germ_mem_radical_nonRegularIdeal hS hX V g hg x hxV
    obtain ⟨-, -, g', hg', hrange, hgy⟩ :=
      MMP.Resolution.isReduced_adicCompletion_stalk_and_normalization_completion S sX hX x
    have hmodel : ∃ P : Ideal (AdicCompletion (maximalIdeal (S.presheaf.stalk x))
        (S.presheaf.stalk x)), IsModelSingularIdeal _ P := by
      rcases hS.2 x hxc with h | h | h
      · exact absurd h hsm
      · obtain ⟨e⟩ := h.2.2
        exact ⟨_, Or.inl ⟨e.toRingEquiv, rfl⟩⟩
      · obtain ⟨e⟩ := h.2.2.2
        exact ⟨_, Or.inr ⟨e.toRingEquiv, rfl⟩⟩
    obtain ⟨P, hP⟩ := hmodel
    exact mem_range_of_model _ _ hexc.1.2.1 g' hg' hrange hgy P hP _ hrad

/-- **The conductor core.** A section of `𝒪_{S^ν}` over `ν⁻¹V` vanishing on `D^ν` lies in the
image of `Γ(S, V)`: the ideal of `D^ν` is the conductor. -/
private theorem conductor_core
    {S : Scheme.{0}} {sX : S ⟶ Spec (.of ℂ)} (hS : IsSemismooth sX 2)
    (hX : ∀ U : S.Opens, IsCompact (U : Set S) → (irreducibleComponents U).Finite)
    (V : S.Opens)
    (g : Γ(Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX,
      Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ V))
    (hg : ((Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹'
            (smoothLocus sX : Set S)ᶜ,
          (smoothLocus sX).isOpen.isClosed_compl.preimage
            (Stacks.AlgebraicGeometry.Normalization.normalization S hX).continuous⟩).subschemeι.app
        (Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ V)).hom g = 0) :
    g ∈ Set.range ((Stacks.AlgebraicGeometry.Normalization.normalization S hX).app V).hom := by
  have hred : IsReduced S := hS.1.2.1
  have : LocallyOfFiniteType sX := hS.1.1.2.1
  have : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sX
  let _ := Stacks.AlgebraicGeometry.Normalization.quasiCompact_fromGenericPointResidueFields S hX
  refine range_of_local _
      (fun W => Stacks.AlgebraicGeometry.Normalization.injective_fromNormalization_app
      (Stacks.AlgebraicGeometry.Normalization.fromGenericPointResidueFields S) W) V g fun x hx => ?_
  exact exists_local_of_closed _ V g
    (fun y hy hyc => local_preimage_of_germ_mem_range hX y V hy g
      (germ_mem_range hS hX V g hg y hy hyc)) x hx

/-- **The conductor equalizer of a semismooth surface.** Let `S` be a semismooth surface over
`ℂ`, `ν : S^ν ⟶ S` its normalization, `D` the singular locus of `S` with its reduced structure,
`D^ν` the reduced preimage `ν⁻¹(D)`, `π : D^ν ⟶ D` the induced map and `τ` the covering
involution of `π` (an involution over `D` whose invariant functions are those of `D`). Then for
every open `U ⊆ S`, a section `g ∈ Γ(S^ν, ν⁻¹U)` lies in the image of `Γ(S, U)` if and only if its
restriction to `D^ν` is `τ`-invariant. -/
@[mmp "lem_mmp_surface_semismooth_conductor_equalizer"]
public theorem IsSemismooth.mem_range_normalization_app_iff
    {S : Scheme.{0}} {sX : S ⟶ Spec (.of ℂ)} (hS : IsSemismooth sX 2)
    (hX : ∀ U : S.Opens, IsCompact (U : Set S) → (irreducibleComponents U).Finite)
    (π : (Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹'
            (smoothLocus sX : Set S)ᶜ,
          (smoothLocus sX).isOpen.isClosed_compl.preimage
            (Stacks.AlgebraicGeometry.Normalization.normalization S hX).continuous⟩).subscheme ⟶
        (Scheme.IdealSheafData.vanishingIdeal
          ⟨(smoothLocus sX : Set S)ᶜ, (smoothLocus sX).isOpen.isClosed_compl⟩).subscheme)
    (hπ : π ≫ Scheme.IdealSheafData.subschemeι _ =
      Scheme.IdealSheafData.subschemeι _ ≫
        Stacks.AlgebraicGeometry.Normalization.normalization S hX)
    (τ : (Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹'
            (smoothLocus sX : Set S)ᶜ,
          (smoothLocus sX).isOpen.isClosed_compl.preimage
            (Stacks.AlgebraicGeometry.Normalization.normalization S hX).continuous⟩).subscheme ⟶
        (Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹'
            (smoothLocus sX : Set S)ᶜ,
          (smoothLocus sX).isOpen.isClosed_compl.preimage
            (Stacks.AlgebraicGeometry.Normalization.normalization S hX).continuous⟩).subscheme)
    (hτπ : τ ≫ π = π) (hττ : τ ≫ τ = 𝟙 _)
    (hτ : ∀ (V : Opens _) (h : Γ((Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹'
            (smoothLocus sX : Set S)ᶜ,
          (smoothLocus sX).isOpen.isClosed_compl.preimage
            (Stacks.AlgebraicGeometry.Normalization.normalization S hX).continuous⟩).subscheme,
                π ⁻¹ᵁ V)),
      h ∈ Set.range (π.app V).hom ↔
        ∀ (W : Opens _) (h₁ : W ≤ π ⁻¹ᵁ V) (h₂ : W ≤ τ ⁻¹ᵁ (π ⁻¹ᵁ V)),
          ((Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹'
            (smoothLocus sX : Set S)ᶜ,
          (smoothLocus sX).isOpen.isClosed_compl.preimage
            (Stacks.AlgebraicGeometry.Normalization.normalization S
                hX).continuous⟩).subscheme.presheaf.map (homOfLE h₁).op).hom h =
                (τ.appLE (π ⁻¹ᵁ V) W h₂).hom h)
    (U : S.Opens)
    (g : Γ(Stacks.AlgebraicGeometry.Normalization.normalizationScheme S hX,
      Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ U)) :
    g ∈ Set.range ((Stacks.AlgebraicGeometry.Normalization.normalization S hX).app U).hom ↔
      ∀ (W : Opens (Scheme.IdealSheafData.vanishingIdeal
          ⟨(Stacks.AlgebraicGeometry.Normalization.normalization S hX).base ⁻¹'
            (smoothLocus sX : Set S)ᶜ,
          (smoothLocus sX).isOpen.isClosed_compl.preimage
            (Stacks.AlgebraicGeometry.Normalization.normalization S hX).continuous⟩).subscheme)
        (h₁ : W ≤ Scheme.IdealSheafData.subschemeι _ ⁻¹ᵁ
          (Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ U))
        (h₂ : W ≤ (τ ≫ Scheme.IdealSheafData.subschemeι _) ⁻¹ᵁ
          (Stacks.AlgebraicGeometry.Normalization.normalization S hX ⁻¹ᵁ U)),
        ((Scheme.IdealSheafData.subschemeι _).appLE _ W h₁).hom g =
          ((τ ≫ Scheme.IdealSheafData.subschemeι _).appLE _ W h₂).hom g := by
  haveI : IsReduced S := hS.1.2.1
  letI := Stacks.AlgebraicGeometry.Normalization.quasiCompact_fromGenericPointResidueFields S hX
  refine ⟨?_, range_of_invariant _ _ _ π τ hπ
    (Stacks.AlgebraicGeometry.Normalization.injective_fromNormalization_app
      (Stacks.AlgebraicGeometry.Normalization.fromGenericPointResidueFields S))
    (Scheme.IdealSheafData.subschemeι_app_surjective _) (fun V g hg => conductor_core hS hX V g hg)
    hτ U g⟩
  rintro ⟨f, rfl⟩ W h₁ h₂
  exact appLE_app_eq_of_comp_eq _ _ _ (by rw [Category.assoc, ← hπ, ← Category.assoc, hτπ]) U W
    h₁ h₂ f

end MMP.Flips
