module

public import MMP.AlgebraicGeometry.DeRham.LogCartierSheaf
public import MMP.AlgebraicGeometry.DeRham.FormsSectionsAlgebra
public import MMP.AlgebraicGeometry.DeRham.LogCartierEtale
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
public import StacksFrontier.AlgebraicGeometry.Frobenius
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated

/-!
# The inverse Cartier relation on a smooth variety with a normal crossing divisor

Let `k` be a perfect field of characteristic `p`, `V` a smooth proper `k`-scheme of dimension
`n < p` with absolute Frobenius `F`, `S = ⋃ⱼ V(Jⱼ)` a simple normal crossing divisor with
complement `U`, and `K^•` the sheaves of logarithmic forms `Ω^•_{V/k}(log S)`, presented by
injections `e : Γ(K^q, W) → Γ(Ω^q_{V/k}, W ∩ U)` and a differential `d` on `F_*K^•` compatible
with the de Rham differential (`MMP.DeRham.FrobeniusSplittingData`, the data of the
Deligne–Illusie decomposition).

A section `s` of `K^q` over `W` and a section `z` of `F_*K^q` over `W` are related,
`cartierRep q W s z`, when on every affine open `W'' ⊆ W ∩ U` the form `z` represents the inverse
Cartier image `C⁻¹ s` of `s` in the cohomology of the Frobenius-twisted de Rham complex of
`Γ(V, W'')` (`MMP.DeRham.IsInvCartierRep`). Only forms on `U` enter, so no log poles appear. This
relation is stable under restriction, related sections are cycles of `F_*K^•`, and a section
represented by a boundary vanishes, by the injectivity of the inverse Cartier map of a smooth
algebra. Together with the local existence of representatives and the compatibility of a morphism
`c : K^q ⟶ ℋ^q(F_*K^•)` with representatives, the relation is a local description of `c`
(`MMP.DeRham.FrobeniusSplittingData.isLocalCohomologyRep_cartierRep`), so `c` is an isomorphism.

## Main definitions

* `MMP.DeRham.FrobeniusSplittingData`: the data of the Deligne–Illusie decomposition.
* `MMP.DeRham.FrobeniusSplittingData.complex`: the complex `F_*K^•` of sheaves on `V`.
* `MMP.DeRham.FrobeniusSplittingData.cartierRep`: `z` represents `C⁻¹ s` on every affine open of
  `W ∩ U`.

## Main results

* `MMP.DeRham.eq_zero_of_isInvCartierRep_zero_of_smooth`: the inverse Cartier map of a smooth
  algebra over a perfect field is injective.
* `MMP.DeRham.FrobeniusSplittingData.cartierRep_d_eq_zero`: representatives are cycles.
* `MMP.DeRham.FrobeniusSplittingData.cartierRep_eq_zero_of_complex_d`: a section represented by a
  boundary vanishes.
* `MMP.DeRham.FrobeniusSplittingData.isLocalCohomologyRep_cartierRep`: the relation locally
  represents `c`, given the compatibility of `c` and the local existence of representatives.
* `MMP.DeRham.FrobeniusSplittingData.isIso_of_isLocalCohomologyRep_extend`: the same criterion
  for the cohomology of the extension of `F_*K^•` to a `ℤ`-indexed complex.

## Implementation notes

The inverse Cartier relation quantifies over the affine opens `W''` whose ring of functions has
characteristic `p`, that is, the nonempty ones; on an affine open with zero ring of functions all
forms vanish. Sections of `F_*K^q` over `W` are sections of `K^q` over `F⁻¹W = W`.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §4.2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius

universe u v

namespace MMP.DeRham

open KaehlerDifferential KaehlerDifferential.Cartier in
/-- **The inverse Cartier map of a smooth algebra over a perfect field is injective.** -/
theorem eq_zero_of_isInvCartierRep_zero_of_smooth (p : ℕ) [Fact p.Prime] {k L : Type u}
    [Field k] [CharP k p] [PerfectRing k p] [CommRing L] [Algebra k L] [Algebra.Smooth k L]
    [CharP L p] {i : ℕ} {ω : ⋀[L]^i (Ω[L⁄k])} (h : IsInvCartierRep p i ω 0) : ω = 0 := by
  let t : Empty → L := Empty.elim
  have : IsLocalization.Away (∏ j, t j) L := by
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact IsLocalization.self (by
      rintro _ ⟨m, rfl⟩
      simp)
  refine eq_zero_of_isInvCartierRep_zero p (B := L) (u := t) (fun j ↦ j.elim) (fun 𝔪 h𝔪 ↦ ?_) ω h
  obtain ⟨f₀, hf₀, n, s, ε, hs, het⟩ := exists_etale_mvPolynomial_fin (k := k) t
    (fun 𝔭 ↦ linearIndependent_empty_type) ⟨𝔪, h𝔪.isPrime⟩
  exact exists_isLocalLogCartier_of_etale p (L := L) t 𝔪 hf₀ s ε hs het

/-- **The data of the Deligne–Illusie decomposition**: a smooth proper `k`-scheme `V` of dimension
`n < p` in characteristic `p`, a simple normal crossing family `J` of smooth divisors with
complement `U`, a lifting `𝒱` of `V` and of the divisors over `W₂(k)`, sheaves `K q` with
injections `e q W` into the forms on `W ⊓ U` cutting out the forms with logarithmic poles along
`J`, and a differential `d` on `F_*K^•` which `e` carries to the de Rham differential. -/
structure FrobeniusSplittingData (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] [PerfectField k]
    (n : ℕ) {V : Scheme.{u}} (f : V ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension n f]
    (ι : Type v) [Fintype ι] [HasDerivedCategory.{u} V.Modules] where
  /-- The dimension is smaller than the characteristic. -/
  hpn : n < p
  /-- `V` has characteristic `p`. -/
  hV : IsInCharacteristic V p
  /-- The components of the divisor. -/
  J : ι → V.IdealSheafData
  /-- The divisor has simple normal crossings. -/
  hJ : ∀ T : Finset ι,
    SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, J j).subschemeι ≫ f) ∧
    (n < T.card → IsEmpty (⨆ j ∈ T, J j).subscheme)
  /-- The lifting of `V` over `W₂(k)`. -/
  𝒱 : Scheme.{u}
  /-- The structure morphism of the lifting. -/
  g : 𝒱 ⟶ Spec (.of (TruncatedWittVector p 2 k))
  /-- The liftings of the components. -/
  I : ι → 𝒱.IdealSheafData
  /-- The reduction `W₂(k) → k`. -/
  π : TruncatedWittVector p 2 k →+* k
  /-- The reduction is the first Witt coefficient. -/
  hπ : ∀ x, π x = x.coeff 0
  /-- The closed immersion of `V` in its lifting. -/
  i : V ⟶ 𝒱
  /-- `V` is the reduction of `𝒱` modulo `p`. -/
  hi : IsPullback i f g (Spec.map (CommRingCat.ofHom π))
  /-- The components are the reductions of their liftings. -/
  hIJ : ∀ j, ∃ φ, IsPullback φ (J j).subschemeι (I j).subschemeι i
  /-- The lifted divisor has simple normal crossings over `W₂(k)`. -/
  hI : ∀ T : Finset ι,
    SmoothOfRelativeDimension (n - T.card) ((⨆ j ∈ T, I j).subschemeι ≫ g) ∧
    (n < T.card → IsEmpty (⨆ j ∈ T, I j).subscheme)
  /-- The complement of the divisor. -/
  U : V.Opens
  /-- `U` is the complement of the divisor. -/
  hU : U = ((⨅ j, J j).support).compl
  /-- The sheaves of logarithmic forms. -/
  K : ℕ → V.Modules
  /-- The restriction of logarithmic forms to the complement of the divisor. -/
  e : ∀ (q : ℕ) (W : V.Opens), Γ(K q, W) →+ Γ(f.relativeDifferentialForms (q : ℤ), W ⊓ U)
  /-- A logarithmic form is determined by its restriction to `U`. -/
  he_inj : ∀ (q : ℕ) W, Function.Injective (e q W)
  /-- The restriction is linear. -/
  he_smul : ∀ (q : ℕ) W (a : Γ(V, W)) (s : Γ(K q, W)),
    e q W (a • s) = V.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op a • e q W s
  /-- The restriction commutes with restriction to smaller opens. -/
  he_res : ∀ (q : ℕ) (W₁ W₂ : V.Opens) (h : W₁ ≤ W₂) (s : Γ(K q, W₂)),
    e q W₁ ((K q).presheaf.map (homOfLE h).op s) =
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (inf_le_inf_right _ h)).op (e q W₂ s)
  /-- The image of `e` consists of the forms `ω` with logarithmic poles: `fω` and `f dω` extend
  for every local equation `f` of the divisor. -/
  he_range : ∀ (q : ℕ) (W : V.Opens) (ω : Γ(f.relativeDifferentialForms (q : ℤ), W ⊓ U)),
    ω ∈ Set.range (e q W) ↔
      ∀ (W' : V.affineOpens) (hW' : (W' : V.Opens) ≤ W) (c : ι → Γ(V, W')),
        (∀ j, c j ∈ (J j).ideal W') →
        (∃ η : Γ(f.relativeDifferentialForms (q : ℤ), W'),
          (f.relativeDifferentialForms (q : ℤ)).presheaf.map
              (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op η =
            V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op (∏ j, c j) •
              (f.relativeDifferentialForms (q : ℤ)).presheaf.map
                (homOfLE (inf_le_inf_right U hW')).op ω) ∧
        (∃ η : Γ(f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ), W'),
          (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
              (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op η =
            V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op (∏ j, c j) •
              (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map
                (homOfLE (inf_le_inf_right U hW')).op
                  (((f.deRhamComplex).d q (q + 1)).val.app (op (W ⊓ U)) ω))
  /-- The differential of `F_*K^•`. -/
  d : ∀ q : ℕ, (Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj (K q) ⟶
    (Scheme.Modules.pushforward (absoluteFrobenius V p hV)).obj (K (q + 1))
  /-- `d ∘ d = 0`. -/
  hd : ∀ q : ℕ, d q ≫ d (q + 1) = 0
  /-- `e` carries `d` to the de Rham differential. -/
  he_d : ∀ (q : ℕ) (W : V.Opens) (s : Γ(K q, absoluteFrobenius V p hV ⁻¹ᵁ W)),
    e (q + 1) (absoluteFrobenius V p hV ⁻¹ᵁ W) ((d q).app W s) =
      ((f.deRhamComplex).d q (q + 1)).val.app (op (absoluteFrobenius V p hV ⁻¹ᵁ W ⊓ U))
        (e q _ s)

namespace FrobeniusSplittingData

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{u}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type v} [Fintype ι] [HasDerivedCategory.{u} V.Modules]
  (D : FrobeniusSplittingData p k n f ι)

/-- The complex `F_*K^•` of sheaves of modules on `V`. -/
abbrev complex : CochainComplex V.Modules ℕ :=
  CochainComplex.of (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q))
    D.d D.hd

/-- **The inverse Cartier relation**: on every affine open `W'' ⊆ W ⊓ U` of characteristic `p`,
the restriction of `z` represents the inverse Cartier image of the restriction of `s`. -/
def cartierRep (q : ℕ) (W : V.Opens) (s z : Γ(D.K q, W)) : Prop :=
  ∀ (W'' : V.affineOpens) (h : (W'' : V.Opens) ≤ W ⊓ D.U) [CharP Γ(V, W'') p],
    letI := MMP.Mori.sectionAlgebra f W''
    IsInvCartierRep p q
      (formsAlgEquiv f q W''
        ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op (D.e q W s)))
      (formsAlgEquiv f q W''
        ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op (D.e q W z)))

/-- Restricting a logarithmic form to `W'` and then its image to `A ⊆ W' ⊓ U` is restricting its
image to `A`. -/
theorem map_e_map (q : ℕ) {W W' : V.Opens} (h : W' ≤ W) {A : V.Opens} (hA : A ≤ W' ⊓ D.U)
    (s : Γ(D.K q, W)) :
    (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op
        (D.e q W' ((D.K q).presheaf.map (homOfLE h).op s)) =
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (hA.trans (inf_le_inf_right _ h))).op (D.e q W s) := by
  rw [D.he_res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The inverse Cartier relation is stable under restriction. -/
theorem cartierRep_restrict (q : ℕ) {W W' : V.Opens} (h : W' ≤ W) {s z : Γ(D.K q, W)}
    (hr : D.cartierRep q W s z) :
    D.cartierRep q W' ((D.K q).presheaf.map (homOfLE h).op s)
      ((D.K q).presheaf.map (homOfLE h).op z) := by
  intro A hA _
  rw [D.map_e_map q h hA, D.map_e_map q h hA]
  exact hr A _

/-- A form on `W ⊓ U` which vanishes on every affine open of `W ⊓ U` with nonzero ring of
functions vanishes. -/
theorem eq_zero_of_forall_affineOpens (q : ℕ) {W : V.Opens}
    (ω : Γ(f.relativeDifferentialForms (q : ℤ), W ⊓ D.U))
    (hω : ∀ (A : V.affineOpens) (hA : (A : V.Opens) ≤ W ⊓ D.U), Nontrivial Γ(V, A) →
      (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op ω = 0) : ω = 0 := by
  refine Stacks.Algebraization.eq_zero_of_affine_cover ω (fun _ : Unit ↦ (⊤ : V.Opens))
    (by simp) fun A _ hA _ ↦ ?_
  change (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op ω = 0
  rcases subsingleton_or_nontrivial Γ(V, A) with hL | hL
  · let := MMP.Mori.sectionAlgebra f A
    refine (formsAlgEquiv f q A).map_eq_zero_iff.1 ?_
    have : Subsingleton (⋀[Γ(V, A)]^q (Ω[Γ(V, A)⁄k])) := Module.subsingleton Γ(V, A) _
    exact Subsingleton.elim _ _
  · exact hω A hA hL

/-- **Representatives are cycles.** -/
theorem cartierRep_d_eq_zero (q : ℕ) {W : V.Opens} {s z : Γ(D.K q, W)}
    (hr : D.cartierRep q W s z) : (D.d q).app W z = 0 := by
  refine D.he_inj (q + 1) W ((D.he_d q W z).trans ?_ |>.trans (map_zero _).symm)
  change ((f.deRhamComplex).d q (q + 1)).val.app (op (W ⊓ D.U)) (D.e q W z) = 0
  refine D.eq_zero_of_forall_affineOpens (q + 1) _ fun A hA hL ↦ ?_
  have : CharP Γ(V, A) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (cast_eq_zero_of_isInCharacteristic D.hV _)
  let := MMP.Mori.sectionAlgebra f A
  have hnat : (f.relativeDifferentialForms ((q + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hA).op
      (((f.deRhamComplex).d q (q + 1)).val.app (op (W ⊓ D.U)) (D.e q W z)) =
      ((f.deRhamComplex).d q (q + 1)).val.app (op A)
        ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op (D.e q W z)) :=
    (PresheafOfModules.naturality_apply ((f.deRhamComplex).d q (q + 1)).val (homOfLE hA).op _).symm
  have h5 : formsAlgEquiv f (q + 1) A (((f.deRhamComplex).d q (q + 1)).val.app (op A)
    ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op (D.e q W z))) = 0 :=
    (formsAlgEquiv_d f q A _).trans (hr A hA).deRhamDifferential_eq_zero
  exact hnat.trans ((formsAlgEquiv f (q + 1) A).map_eq_zero_iff.1 h5)

/-- A logarithmic form whose restriction to every affine open of `W ⊓ U` of characteristic `p`
has vanishing inverse Cartier image vanishes. -/
theorem eq_zero_of_forall_isInvCartierRep_zero (q : ℕ) {W : V.Opens} (s : Γ(D.K q, W))
    (h : ∀ (A : V.affineOpens) (hA : (A : V.Opens) ≤ W ⊓ D.U) [CharP Γ(V, A) p],
      letI := MMP.Mori.sectionAlgebra f A
      IsInvCartierRep p q (formsAlgEquiv f q A
        ((f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op (D.e q W s))) 0) :
    s = 0 := by
  refine D.he_inj q W (Eq.trans ?_ (map_zero _).symm)
  refine D.eq_zero_of_forall_affineOpens q _ fun A hA hL ↦ ?_
  have : CharP Γ(V, A) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (cast_eq_zero_of_isInCharacteristic D.hV _)
  let := MMP.Mori.sectionAlgebra f A
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : Algebra.Smooth k Γ(V, A) := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra f A.2
  exact (formsAlgEquiv f q A).map_eq_zero_iff.1
    (eq_zero_of_isInvCartierRep_zero_of_smooth p (h A hA))

/-- A section represented by `0` vanishes. -/
theorem cartierRep_eq_zero_of_zero (q : ℕ) {W : V.Opens} {s : Γ(D.K q, W)}
    (hr : D.cartierRep q W s 0) : s = 0 := by
  refine D.eq_zero_of_forall_isInvCartierRep_zero q s fun A hA _ ↦ ?_
  let := MMP.Mori.sectionAlgebra f A
  have h0 : (f.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE hA).op
      (D.e q W 0) = 0 := by rw [map_zero, map_zero]
  have h1 : formsAlgEquiv f q A ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE hA).op (D.e q W 0)) = 0 := (formsAlgEquiv f q A).map_eq_zero_iff.2 h0
  have h := hr A hA
  rwa [h1] at h

/-- A section represented by `d y` vanishes. -/
theorem cartierRep_eq_zero_of_d (i : ℕ) {W : V.Opens} {s : Γ(D.K (i + 1), W)}
    (y : Γ(D.K i, W)) (hr : D.cartierRep (i + 1) W s ((D.d i).app W y)) : s = 0 := by
  refine D.eq_zero_of_forall_isInvCartierRep_zero (i + 1) s fun A hA _ ↦ ?_
  let := MMP.Mori.sectionAlgebra f A
  have he : D.e (i + 1) W ((D.d i).app W y) =
      ((f.deRhamComplex).d i (i + 1)).val.app (op (W ⊓ D.U)) (D.e i W y) := D.he_d i W y
  have hnat : (f.relativeDifferentialForms ((i + 1 : ℕ) : ℤ)).presheaf.map (homOfLE hA).op
      (((f.deRhamComplex).d i (i + 1)).val.app (op (W ⊓ D.U)) (D.e i W y)) =
      ((f.deRhamComplex).d i (i + 1)).val.app (op A)
        ((f.relativeDifferentialForms (i : ℤ)).presheaf.map (homOfLE hA).op (D.e i W y)) :=
    (PresheafOfModules.naturality_apply ((f.deRhamComplex).d i (i + 1)).val (homOfLE hA).op _).symm
  have h := hr A hA
  rw [he, hnat, formsAlgEquiv_d] at h
  refine h.of_sub_mem_exactForms ?_
  rw [zero_sub, ← map_neg]
  exact (twist_mem_exactForms_iff _).2 (Or.inr ⟨i, _, rfl, rfl⟩)

/-- **A section represented by a boundary of `F_*K^•` vanishes.** -/
theorem cartierRep_eq_zero_of_complex_d {q : ℕ} (i : ℕ) {W : V.Opens} {s : Γ(D.K q, W)}
    (y : Γ(D.K i, W)) (hr : D.cartierRep q W s ((D.complex.d i q).val.app (op W) y)) : s = 0 := by
  by_cases hiq : (ComplexShape.up ℕ).Rel i q
  · obtain rfl : i + 1 = q := hiq
    have hd : D.complex.d i (i + 1) = D.d i := CochainComplex.of_d
      (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q)) D.d i
    have h2 : (D.complex.d i (i + 1)).app W y = (D.d i).app W y := by rw [hd]
    have hr' : D.cartierRep (i + 1) W s ((D.complex.d i (i + 1)).app W y) := hr
    rw [h2] at hr'
    exact D.cartierRep_eq_zero_of_d i y hr'
  · have h2 : (D.complex.d i q).app W y = 0 := by
      rw [D.complex.shape i q hiq]
      rfl
    have hr' : D.cartierRep q W s ((D.complex.d i q).app W y) := hr
    rw [h2] at hr'
    exact D.cartierRep_eq_zero_of_zero q hr'

/-- Representatives are cycles of `F_*K^•`. -/
theorem cartierRep_complex_d_eq_zero {q : ℕ} {W : V.Opens} {s z : Γ(D.K q, W)}
    (hr : D.cartierRep q W s z) : (D.complex.d q (q + 1)).val.app (op W) z = 0 := by
  have hd : D.complex.d q (q + 1) = D.d q := CochainComplex.of_d
    (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q)) D.d q
  have h2 : (D.complex.d q (q + 1)).app W z = (D.d q).app W z := by rw [hd]
  exact h2.trans (D.cartierRep_d_eq_zero q hr)

/-- **The data locally represent a morphism into the cohomology sheaf**: given the
compatibility of `c` with representatives and the local existence statements (P1.5), the
relation `cartierRep` satisfies the local criterion. -/
theorem isLocalCohomologyRep_cartierRep (q : ℕ) (c : D.K q ⟶ D.complex.homology q)
    (class_eq : ∀ {W : V.Opens} {s : Γ(D.K q, W)}
      {z : ToType ((D.complex.cycles q).val.obj (op W))},
      D.cartierRep q W s ((D.complex.iCycles q).val.app (op W) z) →
        c.val.app (op W) s = (D.complex.homologyπ q).val.app (op W) z)
    (exists_rep : ∀ (W : V.Opens) (s : Γ(D.K q, W)) {x : V}, x ∈ W →
      ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧
        ∃ z, D.cartierRep q W' ((D.K q).presheaf.map (homOfLE h).op s) z)
    (exists_rep_of_cycle : ∀ (W : V.Opens) (z : ToType ((D.complex.X q).val.obj (op W))),
      (D.complex.d q (q + 1)).val.app (op W) z = 0 → ∀ {x : V}, x ∈ W →
      ∃ (W' : V.Opens) (h : W' ≤ W), x ∈ W' ∧ ∃ (s : Γ(D.K q, W'))
        (y : ToType ((D.complex.X ((ComplexShape.up ℕ).prev q)).val.obj (op W')))
        (z' : ToType ((D.complex.X q).val.obj (op W'))), D.cartierRep q W' s z' ∧
        (D.complex.X q).val.map (homOfLE h).op z = z' + (D.complex.d _ q).val.app (op W') y) :
    IsLocalCohomologyRep D.complex q c (D.cartierRep q) where
  restrict h _ _ hr := D.cartierRep_restrict q h hr
  d_eq_zero hr := D.cartierRep_complex_d_eq_zero hr
  class_eq := class_eq
  exists_rep := exists_rep
  eq_zero y hr hy := D.cartierRep_eq_zero_of_complex_d _ y (hy ▸ hr)
  exists_rep_of_cycle := exists_rep_of_cycle

/-- **The bridge to the `ℤ`-indexed complex.** A morphism `c` from `K q` into the
`q`-th cohomology sheaf of the extension of `F_*K^•` to `ℤ` is an isomorphism as soon as its
composite with the identification of that cohomology with the cohomology of `F_*K^•` is locally
represented. -/
theorem isIso_of_isLocalCohomologyRep_extend (q : ℕ)
    (c : D.K q ⟶ (D.complex.extend ComplexShape.embeddingUpNat).homology (q : ℤ))
    {Rep : ∀ W : V.Opens, ToType ((D.K q).val.obj (op W)) →
      ToType ((D.complex.X q).val.obj (op W)) → Prop}
    (h : IsLocalCohomologyRep D.complex q
      (c ≫ (D.complex.extendHomologyIso ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ))
        rfl).hom) Rep) :
    IsIso c := by
  let e := D.complex.extendHomologyIso ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) rfl
  have : IsIso (c ≫ e.hom) := h.isIso
  have hc : c = (c ≫ e.hom) ≫ e.inv := by simp
  rw [hc]
  infer_instance

end FrobeniusSplittingData

end MMP.DeRham

end
