module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
import MMP.AlgebraicGeometry.Geometrically.BertiniGenericFibres
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Singularities.CyclicCover.Algebra
import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector

/-!
# Adjunction for a general member of a free linear system on a pair

Let `k` be an algebraically closed field of characteristic zero and `|V|` a free linear system on
a normal variety `X` over `k` with `dim X ≥ 2`, spanned by sections `s₀, …, s_N` of an invertible
sheaf `L`. The general member `H = Z(∑ᵢ cᵢ sᵢ)` of `|V|` is normal. If moreover `(X, Δ)` is a pair,
then for a general member `H` and a connected component `H⁰` of `H`, the scheme `H⁰` is a normal
variety containing no component of `Δ`, and the restriction `Δ|_{H⁰}` (coefficient
`∑_{j : C ⊆ Dⱼ} aⱼ` at a prime divisor `C` of `H⁰`) satisfies adjunction: whenever `m > 0` and
`m(K_X + Δ)` is a Cartier divisor `D`, the divisor `m(K_{H⁰} + Δ|_{H⁰})` is Cartier and
`𝒪_{H⁰}(m(K_{H⁰} + Δ|_{H⁰})) ≅ (𝒪_X(D) ⊗ L^{⊗ m})|_{H⁰} = 𝒪_X(m(K_X + Δ + H))|_{H⁰}`.

The proof of adjunction follows Kollár–Mori. Let `X° ⊆ X` be the largest open subset of the
smooth locus on which `Supp Δ` is a simple normal crossing divisor; it contains every point of
codimension at most one, since at such a point at most one component of `Δ` passes and that
component is generically smooth. For general `H` the member `H` is normal, contains no component
of `Δ` and no irreducible component of `X ∖ X°`, and `H ∩ X°` together with the components of `Δ`
is a simple normal crossing family on `X°`. As `H` is an effective Cartier divisor, a point of
`H⁰` has codimension in `X` one more than in `H⁰`; hence `V = H⁰ ∩ X°` contains every point of
codimension one of `H⁰`, and `dim H⁰ = dim X - 1`. On `V` each component `E` of `Δ` restricts
with multiplicity one: at the generic point `η` of a prime divisor of `V` lying on `E`, regular
parameters `z_H, z_E` of `𝒪_{X,η}` cut out `H` and `E`, the local ring `𝒪_{V,η} = 𝒪_{X,η}/(z_H)`
is a discrete valuation ring, and `z_E` restricts to a uniformizer. Adjunction for the smooth
hypersurface `H ∩ X°` of the smooth variety `X°`, `𝒪_{H ∩ X°}(K) ≅ (ω_{X°} ⊗ L)|_{H ∩ X°}`, then
identifies the divisorial sheaf of `m(K_{H⁰} + Δ|_{H⁰})` with the pull-back of
`𝒪_X(m(K_X + Δ)) ⊗ L^{⊗ m}` on `V`. That pull-back is the divisorial sheaf of a Cartier divisor
`E₀` of `H⁰`, and two divisors whose divisorial sheaves agree off a closed subset of codimension
at least two are linearly equivalent; so `m(K_{H⁰} + Δ|_{H⁰})` is linearly equivalent to `E₀`,
which gives both conclusions.

## Main results

* `MMP.Threefold.Bridges.exists_dense_open_isNormal_zeroScheme_of_two_le_topologicalKrullDim`:
  the general member of a free linear system on a normal variety is normal.
* `MMP.Mori.exists_isSNC_restrictOpen_of_isNormalVariety`: on a normal variety over a perfect
  field, there is an open of the smooth locus on which `Δ` is snc containing every point of
  codimension at most one.
* `MMP.Mori.IsPair.exists_dense_open_adjunction_connectedComponent_zeroScheme`: adjunction for a
  connected component of a general member.
* `MMP.Mori.DivisorWithCoeffs.IsSNC.isSNCFamily_idealSheaf`: the components of an snc divisor
  form an snc family.
* `MMP.Mori.Divisor.IsCartier.nonempty_divisorialSheaf_zsmul_add_iso`: for Cartier divisors
  `A`, `B`, `𝒪(mA + B) ≅ 𝒪(A)^{⊗ m} ⊗ 𝒪(B)`.

## Implementation notes

The system `V` is presented by sections `s₀, …, s_N` spanning it, the member of `|V|` attached to a
nonzero coefficient vector `c ∈ kᴺ⁺¹` is the zero scheme of
`MMP.Threefold.Bridges.systemSection s c = ∑ᵢ cᵢ sᵢ`, and "general" means: for `[c]` in a dense
open of `|V| = ℙ(V)`, which is
`AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)`, the vector `c`
giving the point `MMP.Threefold.Bridges.dualPoint c`. Freeness of the system is that the
non-vanishing loci of the sections of `V` cover `X`. A member is not required to be connected or
irreducible; a connected component of `H` is a nonempty connected clopen subset of `H`, taken as an
open subscheme. Since `𝒪_X(H) ≅ L`, the sheaf `𝒪_X(m(K_X + Δ + H))` is written `𝒪_X(D) ⊗ L^{⊗ m}`
with `D = m(K_X + Δ)`. Canonical divisors of `X` and of `H⁰` are arbitrary: the conclusion holds
for every choice.

The adjunction formula is proved for the zero scheme `T = Z(s)` of a nonzero section of an
invertible sheaf `M` on a smooth integral scheme `Y`: the conormal sequence
`0 ⟶ 𝒞_{T/Y} ⟶ i^*Ω_{Y/k} ⟶ Ω_{T/k} ⟶ 0` is short exact because `T` is smooth, its conormal
sheaf is `i^*ℐ_T`, and `ℐ_T ≅ M^∨` because `s` is a nonzerodivisor; taking determinants gives
`i^*(Ω^{n+1}_{Y/k} ⊗ M) ≅ Ω^n_{T/k}`.

The extension across the complement of `V` is done for divisors rather than for reflexive
sheaves: the divisorial sheaf of `m(K_{H⁰} + Δ|_{H⁰})` and that of the Cartier divisor `E₀` agree
on `V`, which contains the generic point of every prime divisor of `H⁰`, so the two divisors are
linearly equivalent.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 5.17
* [R. Hartshorne, *Algebraic geometry*][Har77], II.8.20
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace MMP.Threefold.Bridges

attribute [local instance] globalSectionsModule

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-- **General members of a free linear system on a normal variety are normal.** Let `k` be
algebraically closed of characteristic zero, `X` a normal variety over `k` with `dim X ≥ 2`, `L`
an invertible sheaf on `X`, and `|V|` the free linear system of the span `V` of
`s₀, …, s_N ∈ H⁰(X, L)`. There is a dense open `U ⊆ ℙ(V)` such that for every nonzero `c` with
`[c] ∈ U` the member `Z(∑ᵢ cᵢ sᵢ)` is normal. -/
@[mmp "lem_mmp_foundation_km5d_normal_bertini"]
public theorem exists_dense_open_isNormal_zeroScheme_of_two_le_topologicalKrullDim
    [IsAlgClosed k] [CharZero k] [IsVariety k (X ↘ Spec (.of k))] [IsNormal X]
    (hdim : 2 ≤ topologicalKrullDim X)
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        IsNormal (Stacks.Divisors.zeroScheme X L (systemSection s c)).subscheme :=
  (exists_dense_open_isNormal_zeroScheme s hs).2

end MMP.Threefold.Bridges

namespace MMP.Mori

open MMP.Threefold.Bridges Opposite

/-! ### Generalities on schemes -/

section General

/-- A connected normal scheme with finitely many irreducible components is irreducible: its
irreducible components are pairwise disjoint, hence open. -/
private theorem irreducibleSpace_of_isNormal_of_connectedSpace {Y : Scheme.{u}} [IsNormal Y]
    [NoetherianSpace Y] [ConnectedSpace Y] : IrreducibleSpace Y := by
  classical
  obtain ⟨y⟩ : Nonempty Y := ConnectedSpace.toNonempty
  let C : irreducibleComponents Y :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  have : Finite (irreducibleComponents Y) :=
    (NoetherianSpace.finite_irreducibleComponents (α := Y)).to_subtype
  have hC : IsClopen (C.1 : Set Y) := by
    refine ⟨isClosed_of_mem_irreducibleComponents _ C.2, ?_⟩
    have hcl : IsClosed (⋃ D ∈ {D : irreducibleComponents Y | D ≠ C}, (D.1 : Set Y)) :=
      (Set.toFinite {D : irreducibleComponents Y | D ≠ C}).isClosed_biUnion fun D _ =>
        isClosed_of_mem_irreducibleComponents _ D.2
    convert hcl.isOpen_compl using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, not_exists,
      not_and]
    refine ⟨fun hx D hD hxD => hD (MMP.Mori.eq_of_mem_irreducibleComponents hxD hx), fun h => ?_⟩
    by_contra hx
    exact h ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
      (fun hD => hx (hD ▸ mem_irreducibleComponent)) mem_irreducibleComponent
  have h := C.2.1
  rw [hC.eq_univ ⟨y, mem_irreducibleComponent⟩] at h
  exact (irreducibleSpace_def Y).2 h

/-- Let `X₀ ⊆ X` be an open subset containing every point of codimension at most one, and `O`
an open subset meeting every irreducible component of `X ∖ X₀`. Then every point of codimension
at most two outside `O` lies in `X₀`: otherwise it specializes from the generic point `ξ` of a
component of `X ∖ X₀`, which lies in `O` and so differs from it, and has codimension at least
two. -/
private theorem mem_of_coheight_le_two {X : Scheme.{u}} [NoetherianSpace X] (X₀ O : X.Opens)
    (hX₀ : ∀ x : X, Order.coheight x ≤ 1 → x ∈ X₀)
    (hO : ∀ Y ∈ MMP.Resolution.componentsOf ((X₀ : Set X)ᶜ), (Y ∩ O).Nonempty)
    {x : X} (hx : Order.coheight x ≤ 2) (hxO : x ∉ O) : x ∈ X₀ := by
  by_contra hx₀
  have hc := X₀.isOpen.isClosed_compl
  obtain ⟨Y, hY, hxY⟩ :=
    Set.mem_sUnion.1 ((MMP.Resolution.Aux.finite_and_cover_componentsOf hc).2 hx₀)
  obtain ⟨ξ, hξX₀, rfl⟩ := MMP.Resolution.Aux.exists_eq_closure_of_mem_componentsOf hc hY
  obtain ⟨z, hzY, hzO⟩ := hO _ hY
  have hξO : ξ ∈ O := (specializes_iff_mem_closure.2 hzY).mem_open O.isOpen hzO
  have hsp : ξ ⤳ x := specializes_iff_mem_closure.2 hxY
  have hlt : x < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hsp) fun h =>
    hxO (((Scheme.le_iff_specializes.1 h).antisymm hsp).eq ▸ hξO)
  have h : Order.coheight ξ + 1 ≤ 1 + 1 := (Order.coheight_add_one_le hlt).trans hx
  exact hξX₀ (hX₀ ξ ((WithTop.add_le_add_iff_right WithTop.one_ne_top).1 h))

/-- The generic point of an irreducible scheme has coheight zero. -/
private theorem coheight_genericPoint_eq_zero (Y : Scheme.{u}) [IrreducibleSpace Y] :
    Order.coheight (genericPoint Y) = 0 :=
  Order.coheight_eq_zero.2 fun b _ =>
    Scheme.le_iff_specializes.2 (_root_.genericPoint_specializes b)

/-- No member of a simple normal crossing family on an irreducible scheme is the zero ideal. -/
private theorem ne_bot_of_isSNCFamily {k : Type u} [Field k] {Y : Scheme.{u}} [IrreducibleSpace Y]
    {s : Y ⟶ Spec (.of k)} {Λ : Type*} {E : Λ → Y.IdealSheafData}
    (h : MMP.Resolution.IsSNCFamily s E) (i : Λ) : E i ≠ ⊥ := by
  intro hbot
  obtain ⟨n₀, z, c, hz, -, -⟩ := h.2 (genericPoint Y)
  have hmem : genericPoint Y ∈ (E i).support := by
    rw [hbot, Scheme.IdealSheafData.support_bot]
    trivial
  have hn0 : n₀ = 0 := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight, coheight_genericPoint_eq_zero] at h
    exact_mod_cast h.symm
  subst hn0
  exact (c ⟨i, hmem⟩).elim0

/-- An open subscheme contained in the smooth locus of `s` is smooth over the base. -/
private theorem smooth_ι_comp_of_le_smoothLocus {Y S : Scheme.{u}} {s : Y ⟶ S}
    [LocallyOfFinitePresentation s] (U : Y.Opens) (h : U ≤ smoothLocus s) : Smooth (U.ι ≫ s) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
    ← MMP.Mori.smoothLocus_eq_smoothLocus]
  exact top_le_iff.1 fun x _ => h x.2

/-- If a closed irreducible subscheme `W` of an integral scheme `Y` of finite type over `k` has
generic point of coheight one, then `dim Y = dim W + 1`. -/
private theorem eq_add_one_of_coheight_genericPoint_eq_one {k : Type u} [Field k]
    {Y W : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    [IrreducibleSpace W] (j : W ⟶ Y) (hj : Topology.IsClosedEmbedding j)
    (hη : Order.coheight (j (genericPoint W)) = 1) {n n' : ℕ}
    (hY : topologicalKrullDim Y = n) (hW : topologicalKrullDim W = n') : n = n' + 1 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (j (genericPoint W))
  rw [hη, hY] at h
  have hcl : closure ({j (genericPoint W)} : Set Y) = Set.range j := by
    have := hj.closure_image_eq ({genericPoint W} : Set W)
    rw [Set.image_singleton] at this
    rw [this, (genericPoint_spec W).def, Set.image_univ]
  have hdimW : topologicalKrullDim (Set.range j) = topologicalKrullDim W := by
    let e := hj.isEmbedding.toHomeomorph
    exact le_antisymm e.symm.isInducing.topologicalKrullDim_le e.isInducing.topologicalKrullDim_le
  rw [hcl, hdimW, hW] at h
  have h' : ((n' + 1 : ℕ) : WithBot ℕ∞) = n := by exact_mod_cast h
  exact_mod_cast h'.symm

end General

/-! ### Local rings of an effective Cartier divisor -/

section CartierStalk

/-- The localization at a prime `q` of `A ⧸ J` is the quotient of the localization of `A` at the
preimage of `q` by the image of `J`. -/
private noncomputable def localizationAtPrimeQuotientEquiv {A : Type*} [CommRing A]
    (J : Ideal A) (q : Ideal (A ⧸ J)) [q.IsPrime] :
    (Localization.AtPrime (q.comap (Ideal.Quotient.mk J))) ⧸
        J.map (algebraMap A (Localization.AtPrime (q.comap (Ideal.Quotient.mk J)))) ≃+*
      Localization.AtPrime q := by
  let p := q.comap (Ideal.Quotient.mk J)
  have hsub : Submonoid.map (Ideal.Quotient.mk J) p.primeCompl = q.primeCompl := by
    change Submonoid.map (Ideal.Quotient.mk J)
      (Submonoid.comap (Ideal.Quotient.mk J) q.primeCompl) = q.primeCompl
    exact Submonoid.map_comap_eq_of_surjective Ideal.Quotient.mk_surjective q.primeCompl
  let _ : IsLocalization (Submonoid.map (Ideal.Quotient.mk J) p.primeCompl)
      (Localization.AtPrime q) := by
    rw [hsub]
    infer_instance
  let ψ : Localization.AtPrime p →+* Localization.AtPrime q :=
    IsLocalization.map (M := p.primeCompl) (Localization.AtPrime q)
      (Ideal.Quotient.mk J) (Submonoid.le_comap_map _)
  have hsurj : Function.Surjective ψ :=
    IsLocalization.map_surjective_of_surjective p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q) (g := Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hker : RingHom.ker ψ = J.map (algebraMap A (Localization.AtPrime p)) := by
    change RingHom.ker (IsLocalization.map (Localization.AtPrime q)
      (Ideal.Quotient.mk J) (Submonoid.le_comap_map _)) = _
    rw [IsLocalization.ker_map (Localization.AtPrime q) (Ideal.Quotient.mk J) rfl]
    simp [Ideal.mk_ker]
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

open CategoryTheory.Limits in
/-- **The local rings of an effective Cartier divisor.** At a point `y` of an effective Cartier
divisor `D` of a locally Noetherian scheme `X`, the dimension of `𝒪_{D,y}` is that of `𝒪_{X,y}`
minus one: `𝒪_{D,y}` is the quotient of `𝒪_{X,y}` by a nonzerodivisor of its maximal ideal. -/
private theorem ringKrullDim_stalk_subscheme_add_one {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (y : I.subscheme) :
    ringKrullDim (I.subscheme.presheaf.stalk y) + 1 =
      ringKrullDim (X.presheaf.stalk (I.subschemeι y)) := by
  have hxSupport : I.subschemeι y ∈ I.supportSet := by
    rw [I.mem_supportSet_iff_mem_support]
    change I.subschemeι y ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact ⟨y, rfl⟩
  obtain ⟨U, hU, hxU, f, hf, e, he⟩ :=
    (Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal I).mp hI _ hxSupport
  let A := Γ(X, U)
  let mk : A →+* A ⧸ Ideal.span {f} := Ideal.Quotient.mk _
  have hyRange : y ∈ Set.range (pullback.fst I.subschemeι U.ι).base := by
    rw [IsOpenImmersion.range_pullbackFst]
    change I.subschemeι y ∈ U.ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    exact hxU
  obtain ⟨z, hz⟩ := Set.mem_range.mp hyRange
  subst hz
  let u : U := (pullback.snd I.subschemeι U.ι).base z
  have hu : (u : X) = I.subschemeι ((pullback.fst I.subschemeι U.ι).base z) := by
    have hh : (pullback.fst I.subschemeι U.ι ≫ I.subschemeι) z =
        (pullback.snd I.subschemeι U.ι ≫ U.ι) z := by rw [pullback.condition]
    simp only [Scheme.Hom.comp_apply] at hh
    exact hh.symm
  let qpt : PrimeSpectrum (A ⧸ Ideal.span {f}) := e.hom z
  have hspec : hU.primeIdealOf u = qpt.comap mk := by
    have hh : (pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom) z =
        (e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) z := by
      rw [he]
    simp only [Scheme.Hom.comp_apply] at hh
    exact hh
  let p : Ideal A := qpt.asIdeal.comap mk
  let _ : p.IsPrime := (qpt.comap mk).2
  let _ : IsNoetherianRing A :=
    (inferInstance : IsLocallyNoetherian X).component_noetherian ⟨U, hU⟩
  let _ : Algebra A (X.presheaf.stalk (u : X)) :=
    X.presheaf.algebra_section_stalk ⟨(u : X), u.2⟩
  let _ : IsLocalization.AtPrime (X.presheaf.stalk (u : X)) p := by
    change IsLocalization.AtPrime (X.presheaf.stalk (u : X)) (qpt.comap mk).asIdeal
    simpa only [← hspec] using hU.isLocalization_stalk u
  let R := Localization.AtPrime p
  let eX := IsLocalization.algEquiv p.primeCompl R (X.presheaf.stalk (u : X))
  let fR : R := algebraMap A R f
  have hfmax : fR ∈ IsLocalRing.maximalIdeal R := by
    have hfp : f ∈ p := by
      change mk f ∈ qpt.asIdeal
      simp [mk]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R p f).2 hfp
  have hfreg : fR ∈ nonZeroDivisors R :=
    IsLocalization.map_nonZeroDivisors_le p.primeCompl R
      (Submonoid.mem_map.mpr ⟨f, isRegular_iff_mem_nonZeroDivisors.mp hf, rfl⟩)
  let Q := R ⧸ Ideal.span {fR}
  let _ : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
    (ne_of_lt (lt_of_le_of_lt (Ideal.span_le.2 (Set.singleton_subset_iff.mpr hfmax))
      (IsLocalRing.maximalIdeal.isMaximal R).lt_top))
  let _ : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {fR})) Ideal.Quotient.mk_surjective
  let eQ : Q ≃+* Localization.AtPrime qpt.asIdeal := by
    have hspan : (Ideal.span {f}).map (algebraMap A R) = Ideal.span {fR} := by
      simp [Ideal.map_span, fR]
    exact (Ideal.quotEquivOfEq hspan.symm).trans
      (localizationAtPrimeQuotientEquiv (Ideal.span {f}) qpt.asIdeal)
  have h₁ : IsOpenImmersion (pullback.fst I.subschemeι U.ι) :=
    @IsOpenImmersion.instFstScheme _ _ _ U.ι I.subschemeι _
  have : IsIso ((pullback.fst I.subschemeι U.ι).stalkMap z) :=
    @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ _ h₁ z
  have : IsIso (e.hom.stalkMap z) :=
    @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ _ (IsOpenImmersion.of_isIso e.hom) z
  let eZ : I.subscheme.presheaf.stalk ((pullback.fst I.subschemeι U.ι).base z) ≃+* Q :=
    (asIso ((pullback.fst I.subschemeι U.ι).stalkMap z)).commRingCatIsoToRingEquiv.trans <|
      (asIso (e.hom.stalkMap z)).commRingCatIsoToRingEquiv.symm.trans <|
        (Spec.stalkIso (.of (A ⧸ Ideal.span {f})) qpt).commRingCatIsoToRingEquiv.trans eQ.symm
  rw [← hu, ringKrullDim_eq_of_ringEquiv eZ, ← ringKrullDim_eq_of_ringEquiv eX.toRingEquiv]
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hfreg hfmax

/-- The coheight of a point of an effective Cartier divisor `D ⊆ X` in `X` is one more than its
coheight in `D`. -/
private theorem coheight_subschemeι_eq_add_one {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (y : I.subscheme) :
    Order.coheight (I.subschemeι y) = Order.coheight y + 1 := by
  have h := ringKrullDim_stalk_subscheme_add_one I hI y
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h.symm

end CartierStalk

/-! ### The open set where the boundary is snc -/

section SNCOpen

/-- A regular local ring `A` with a nonzero element `π` of `𝔪` such that `A ⧸ (π)` is regular
has a regular system of parameters whose first member is `π`. -/
private theorem exists_isRegularSystemOfParameters_zero_eq {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {π : A} (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hreg : IsRegularLocalRing (A ⧸ Ideal.span {π})) :
    ∃ (n : ℕ) (z : Fin (n + 1) → A), MMP.Mori.IsRegularSystemOfParameters z ∧ z 0 = π := by
  classical
  have : IsDomain A := IsRegularLocalRing.isDomain A
  set B := A ⧸ Ideal.span {π}
  set mk : A →+* B := Ideal.Quotient.mk _
  have hsurj : Function.Surjective mk := Ideal.Quotient.mk_surjective
  obtain ⟨n, w, hw⟩ := MMP.Mori.exists_isRegularSystemOfParameters B
  choose w' hw' using fun i => hsurj (w i)
  refine ⟨n, Fin.cons π w', ⟨?_, ?_⟩, rfl⟩
  · have hker : RingHom.ker mk ≤ Ideal.span (Set.range (Fin.cons π w' : Fin (n + 1) → A)) := by
      rw [Ideal.mk_ker]
      exact Ideal.span_mono (Set.singleton_subset_iff.2 ⟨0, rfl⟩)
    have hmap : (Ideal.span (Set.range (Fin.cons π w' : Fin (n + 1) → A))).map mk =
        IsLocalRing.maximalIdeal B := by
      rw [Ideal.map_span, ← hw.1]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self π)]
          exact zero_mem _
        · simp only [Fin.cons_succ, hw']
          exact Ideal.subset_span ⟨j, rfl⟩
      · rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        exact Ideal.subset_span ⟨w' j, ⟨j.succ, by simp⟩, hw' j⟩
    have := Ideal.comap_map_of_surjective' mk hsurj
      (Ideal.span (Set.range (Fin.cons π w' : Fin (n + 1) → A)))
    rw [hmap, sup_eq_left.2 hker] at this
    rw [← this]
    have : IsLocalHom mk := IsLocalHom.of_surjective mk hsurj
    exact IsLocalRing.maximalIdeal_comap mk
  · have hreg0 : π ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hπ0
    rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      hreg0 hπ, hw.2]
    norm_cast

/-- The ideal `I_x ⊆ 𝒪_{X,x}` of the stalk of an ideal sheaf, in the two spellings of the
library. -/
private theorem stalk_eq_stalkIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk I x = I.stalkIdeal x := by
  unfold IdealSheafData.stalk Scheme.IdealSheafData.stalkIdeal
  exact iSup_subtype'

/-- The local ring of a closed subscheme `V(I)` at a point is `𝒪_{X,x} ⧸ I_x`. -/
private noncomputable def stalkSubschemeEquiv {X : Scheme.{u}} (I : X.IdealSheafData)
    (z : I.subscheme) :
    X.presheaf.stalk (I.subschemeι z) ⧸ IdealSheafData.stalk I (I.subschemeι z) ≃+*
      I.subscheme.presheaf.stalk z :=
  (Ideal.quotEquivOfEq (by rw [Scheme.IdealSheafData.ker_stalkMap_subschemeι,
    stalk_eq_stalkIdeal])).trans
    (RingHom.quotientKerEquivOfSurjective
      (SurjectiveOnStalks.stalkMap_surjective I.subschemeι z))

/-- A divisor on a smooth scheme over a perfect field whose support consists of at most one prime
divisor, itself smooth, is snc. -/
private theorem isSNC_of_subsingleton_support {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType g] (hY : IsSmoothScheme g)
    {R : Type*} [Zero R] (D : DivisorWithCoeffs R Y)
    (hD : ∀ E ∈ D.support, ∀ F ∈ D.support, E = F)
    (hsm : ∀ E ∈ D.support, IsSmoothScheme (E.idealSheaf.subschemeι ≫ g)) :
    DivisorWithCoeffs.IsSNC g D := by
  classical
  refine ⟨hsm, fun y => ?_⟩
  have : Smooth g := MMP.Resolution.Aux.smooth_of_isSmoothScheme' g hY
  have := isRegularLocalRing_stalk_of_smooth_over_field g y
  by_cases h : ∃ E ∈ D.support, y ∈ E.support
  · obtain ⟨E, hE, hyE⟩ := h
    obtain ⟨p, hp, hpE⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf g hY E hyE
    have hpm : p ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
      (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support _ _).2 hyE
        (hpE ▸ Ideal.mem_span_singleton_self p)
    have hq : IsRegularLocalRing (Y.presheaf.stalk y ⧸ Ideal.span {p}) := by
      obtain ⟨z, rfl⟩ : y ∈ Set.range E.idealSheaf.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hyE
      have : Smooth (E.idealSheaf.subschemeι ≫ g) :=
        MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ (hsm E hE)
      have := isRegularLocalRing_stalk_of_smooth_over_field (E.idealSheaf.subschemeι ≫ g) z
      exact IsRegularLocalRing.of_ringEquiv ((Ideal.quotEquivOfEq hpE.symm).trans
        (stalkSubschemeEquiv E.idealSheaf z)).symm
    obtain ⟨n, z, hz, hz0⟩ := exists_isRegularSystemOfParameters_zero_eq hpm hp.ne_zero hq
    refine ⟨n + 1, z, fun _ => 0, hz, fun E₁ E₂ _ => Subtype.ext (hD _ E₁.2.1 _ E₂.2.1),
      fun E' => ?_⟩
    rw [hD E'.1 E'.2.1 E hE, hpE, hz0]
  · obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk y)
    exact ⟨n, z, fun E => (h ⟨E.1, E.2.1, E.2.2⟩).elim, hz,
      fun E => (h ⟨E.1, E.2.1, E.2.2⟩).elim, fun E => (h ⟨E.1, E.2.1, E.2.2⟩).elim⟩

/-- On a normal scheme, a point of codimension at most one lying on a prime divisor is its
generic point. -/
private theorem eq_genericPoint_of_mem_support_of_coheight_le_one {X : Scheme.{u}}
    {E : AlgebraicGeometry.PrimeDivisor X} {x : X} (hx : Order.coheight x ≤ 1)
    (hxE : x ∈ E.support) : x = AlgebraicGeometry.PrimeDivisor.genericPoint E := by
  have hsp : E.genericPoint ⤳ x := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
    exact specializes_iff_mem_closure.mpr hxE
  by_contra hne
  have hlt : x < E.genericPoint :=
    lt_of_le_not_ge (Scheme.le_iff_specializes.2 hsp)
      (fun h => hne ((Scheme.le_iff_specializes.1 h).antisymm hsp).eq)
  have h := Order.coheight_add_one_le hlt
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h
  have : (2 : ℕ∞) ≤ 1 := (by norm_num : (2 : ℕ∞) = 1 + 1) ▸ h.trans hx
  exact absurd this (by decide)

/-- On a normal variety over a perfect field, every point of codimension at most one has an open
neighbourhood in the smooth locus on which `Δ` is snc. -/
private theorem exists_isSNC_restrictOpen_nhds {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k f) (Δ : QDivisor X)
    (x : X) (hx : Order.coheight x ≤ 1) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ smoothLocus f ∧ (Δ.restrictOpen V).IsSNC (V.ι ≫ f) := by
  classical
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType f := hX.1.toLocallyOfFiniteType
  -- the non-smooth locus of a prime divisor, as a closed subset of `X`
  let bad : MMP.Mori.PrimeDivisor X → Set X := fun E =>
    E.idealSheaf.subschemeι '' ((smoothLocus (E.idealSheaf.subschemeι ≫ f) : Set _)ᶜ)
  have hbadc : ∀ E, IsClosed (bad E) := fun E =>
    E.idealSheaf.subschemeι.isClosedEmbedding.isClosedMap _
      (smoothLocus (E.idealSheaf.subschemeι ≫ f)).isOpen.isClosed_compl
  have hbadx : ∀ E : MMP.Mori.PrimeDivisor X, x ∈ E.support → x ∉ bad E := by
    rintro E hxE ⟨z, hz, hzx⟩
    have := E.integral
    apply hz
    have hz' : z = genericPoint E.idealSheaf.subscheme := by
      apply E.idealSheaf.subschemeι.isClosedEmbedding.injective
      rw [hzx, eq_genericPoint_of_mem_support_of_coheight_le_one hx hxE]
      have h1 := (genericPoint_spec E.idealSheaf.subscheme).image
        E.idealSheaf.subschemeι.continuous
      rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
        E.idealSheaf.support.isClosed.closure_eq] at h1
      have h2 : IsGenericPoint E.genericPoint (E.support : Set X) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isGenericPoint_closure
      exact h2.eq h1
    rw [hz']
    have : IsLocallyNoetherian E.idealSheaf.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (E.idealSheaf.subschemeι ≫ f)
    exact MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus'
  let C : Set X := ⋃ E ∈ Δ.support, if x ∈ E.support then bad E else (E.support : Set X)
  have hC : IsClosed C := (Δ.support.finite_toSet).isClosed_biUnion fun E _ => by
    split_ifs
    · exact hbadc E
    · exact E.idealSheaf.support.isClosed
  have hxC : x ∉ C := by
    simp only [C, Set.mem_iUnion, not_exists]
    intro E _ h
    split_ifs at h with hxE
    · exact hbadx E hxE h
    · exact hxE h
  have hxsm : x ∈ smoothLocus f := by
    rcases eq_or_lt_of_le hx with h1 | hlt1
    swap
    · have h0 : Order.coheight x = 0 := Order.lt_one_iff.1 hlt1
      have hmax : IsMax x := Order.coheight_eq_zero.1 h0
      have h₁ : genericPoint X ⤳ x := genericPoint_specializes x
      have h₂ : x ⤳ genericPoint X :=
        Scheme.le_iff_specializes.1 (hmax (Scheme.le_iff_specializes.2 h₁))
      rw [(h₂.antisymm h₁).eq]
      exact MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus'
    · have := MMP.Threefold.Mori.CanonUniq.genericPoint_mem_smoothLocus hX.1
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1)
      convert this
      exact (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h1).symm
  let V : X.Opens := smoothLocus f ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
  refine ⟨V, ⟨hxsm, hxC⟩, inf_le_left, ?_⟩
  have hsupp : ∀ W ∈ (Δ.restrictOpen V).support,
      x ∈ (OpenWeilRestriction.primeDivisorMap V.ι W).support ∧
        OpenWeilRestriction.primeDivisorMap V.ι W ∈ Δ.support := by
    intro W hW
    have h0 : (Δ.restrictOpen V) W ≠ 0 := Finsupp.mem_support_iff.mp hW
    have hmem : OpenWeilRestriction.primeDivisorMap V.ι W ∈ Δ.support :=
      Finsupp.mem_support_iff.mpr h0
    refine ⟨?_, hmem⟩
    by_contra hxE
    have hg : (OpenWeilRestriction.primeDivisorMap V.ι W).genericPoint ∈ V := by
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
      exact W.genericPoint.2
    apply hg.2
    refine Set.mem_biUnion hmem ?_
    rw [ite_eq_right hxE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hVsm : IsSmoothScheme (V.ι ≫ f) := by
    rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, ← Scheme.Hom.preimage_smoothLocus_eq,
      ← smoothLocus_eq_smoothLocus, eq_top_iff]
    intro y _
    exact y.2.1
  refine isSNC_of_subsingleton_support (V.ι ≫ f) hVsm _ (fun W₁ h₁ W₂ h₂ => ?_)
    (fun W hW => ?_)
  · obtain ⟨hx₁, -⟩ := hsupp W₁ h₁
    obtain ⟨hx₂, -⟩ := hsupp W₂ h₂
    apply OpenWeilRestriction.primeDivisorMap_injective V.ι
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    rw [← eq_genericPoint_of_mem_support_of_coheight_le_one hx hx₁,
      ← eq_genericPoint_of_mem_support_of_coheight_le_one hx hx₂]
  · obtain ⟨hxE, hE⟩ := hsupp W hW
    refine (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff V.ι f _ W.idealSheaf
      (MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap V.ι W)).2 ?_
    rintro z ⟨v, hv⟩
    by_contra hz
    have hbad : (OpenWeilRestriction.primeDivisorMap V.ι W).idealSheaf.subschemeι z ∈
        bad (OpenWeilRestriction.primeDivisorMap V.ι W) :=
      ⟨z, by rwa [smoothLocus_eq_smoothLocus], rfl⟩
    have hvC : (V.ι v) ∈ C := by
      rw [hv]
      refine Set.mem_biUnion hE ?_
      rw [ite_eq_left hxE]
      exact hbad
    exact v.2.2 hvC

/-- **The snc locus of a boundary contains every point of codimension at most one.** On a normal
variety `X` over a perfect field, there is an open `X₀` of the smooth locus on which a
`ℚ`-divisor `Δ` is snc and which contains every point of codimension at most one. -/
public theorem exists_isSNC_restrictOpen_of_isNormalVariety {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (f : X ⟶ Spec (.of k)) (hX : IsNormalVariety k f) (Δ : QDivisor X) :
    ∃ X₀ : X.Opens, X₀ ≤ smoothLocus f ∧ (Δ.restrictOpen X₀).IsSNC (X₀.ι ≫ f) ∧
      ∀ x : X, Order.coheight x ≤ 1 → x ∈ X₀ := by
  classical
  have : LocallyOfFiniteType f := hX.1.toLocallyOfFiniteType
  have : ∀ E : MMP.Mori.PrimeDivisor X,
      LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ f) := fun E =>
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := E.idealSheaf.subschemeι ≫ f)).mpr
      inferInstance
  let S : Set X.Opens := {V | V ≤ smoothLocus f ∧ (Δ.restrictOpen V).IsSNC (V.ι ≫ f)}
  have hSle : sSup S ∈ S := by
    refine ⟨sSup_le fun V hV => hV.1, ?_⟩
    refine MMP.Threefold.Mori.OpenRestriction.isSNC_restrictOpen_of_cover f (fun V : S => V.1)
      (sSup S) ?_ Δ fun V => V.2.2
    intro x hx
    obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp hx
    exact ⟨⟨V, hV⟩, hxV⟩
  refine ⟨sSup S, hSle.1, hSle.2, fun x hx => ?_⟩
  obtain ⟨V, hxV, hV₁, hV₂⟩ := exists_isSNC_restrictOpen_nhds f hX Δ x hx
  exact (le_sSup (show V ∈ S from ⟨hV₁, hV₂⟩) : V ≤ sSup S) hxV

/-- The components of an snc divisor form an snc family. -/
public theorem DivisorWithCoeffs.IsSNC.isSNCFamily_idealSheaf {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {R : Type*} [Zero R] {D : DivisorWithCoeffs R X}
    (hD : D.IsSNC f) : MMP.Resolution.IsSNCFamily f (fun E : D.support => E.1.idealSheaf) := by
  refine ⟨fun E => ⟨?_, MMP.Resolution.isPureCodimOne_support_primeDivisor E.1, hD.1 E.1 E.2⟩,
    fun x => ?_⟩
  · have := E.1.integral
    infer_instance
  · obtain ⟨n, z, j, hz, hj, hI⟩ := hD.2 x
    exact ⟨n, z, fun E => j ⟨E.1.1, E.1.2, E.2⟩, hz, fun E => hI ⟨E.1.1, E.1.2, E.2⟩,
      fun E E' h => Subtype.ext (Subtype.ext (by simpa using hj h))⟩

end SNCOpen

section OpenRestriction

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

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
/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
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
  Set.eq_univ_of_univ_subset (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

/-- On an irreducible scheme the generic point of every irreducible component is the generic
point. -/
private theorem componentGenericPoint_eq_genericPoint {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z = genericPoint Y := by
  have h1 := isGenericPoint_componentGenericPoint Y Z
  rw [eq_univ_of_irreducibleComponents Z] at h1
  exact h1.eq (genericPoint_spec Y)

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes_component {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem component_specializes_genericPoint {Y : Scheme.{u}} [IrreducibleSpace Y]
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
  (Y.presheaf.stalkSpecializes (genericPoint_specializes_component Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective
      (Y.presheaf.stalkSpecializes (genericPoint_specializes_component Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (component_specializes_genericPoint Z)).hom h
  rwa [TopCat.Presheaf.stalkSpecializes_comp_apply,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes
        (genericPoint_specializes_component E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation, evFF,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

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
  obtain ⟨x, hx, -⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The unique irreducible component `Y` of an irreducible scheme `Y`. -/
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
  fun Z => (U.toScheme.presheaf.stalkSpecializes (component_specializes_genericPoint Z.1)).hom
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
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (component_specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (component_specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes_component _)).hom
      ((X.presheaf.stalkSpecializes (component_specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (component_specializes_genericPoint Z.1)).hom
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
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
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

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- The smooth locus of an open subscheme `U ⊆ X` lies in the smooth locus of `X`. -/
private theorem range_smoothLocus_subset (U : X.Opens) :
    Set.range ((smoothLocus (U.ι ≫ sX)).ι ≫ U.ι) ⊆ Set.range (smoothLocus sX).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 x.2
  let V := (W.ι ≫ U.ι).opensRange
  have e : (W.ι ≫ U.ι).isoOpensRange.inv ≫ (W.ι ≫ U.ι) = V.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hV : Smooth (V.ι ≫ sX) := by
    rw [← e, Category.assoc, Category.assoc]
    infer_instance
  refine le_smoothLocus sX hV ⟨⟨x.1, hxW⟩, rfl⟩

/-- On the smooth locus of a nonempty open subscheme `U`, the divisorial sheaf of `K|_U` is the
canonical sheaf when that of `K` is on the smooth locus of `X`. -/
private theorem nonempty_restrict_smoothLocus_iso {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U] [IsDominant U.ι] :
    Nonempty ((Divisor.divisorialSheaf (K.restrictOpen U)).restrict (smoothLocus (U.ι ≫ sX)).ι ≅
      canonicalSheaf (U.ι ≫ sX) n) := by
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso K U
  let T := smoothLocus (U.ι ≫ sX)
  let S := smoothLocus sX
  let ψ : T.toScheme ⟶ S := IsOpenImmersion.lift S.ι (T.ι ≫ U.ι) (range_smoothLocus_subset U)
  have hψ : ψ ≫ S.ι = T.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso ψ (S.ι ≫ sX)
    (T.ι ≫ U.ι ≫ sX) (by rw [← Category.assoc, hψ, Category.assoc]) n
  exact ⟨(Scheme.Modules.restrictFunctor T.ι).mapIso e₀ ≪≫
    (Scheme.Modules.restrictFunctorComp T.ι U.ι).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorCongr hψ.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp ψ S.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor ψ).mapIso hK.iso ≪≫ e₁⟩

/-- The restriction of a canonical divisor to a nonempty open subscheme is canonical. -/
private theorem isCanonicalDivisor_restrictOpen {n : ℕ} {K : Divisor X}
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] :
    Divisor.IsCanonicalDivisor (U.ι ≫ sX) n (K.restrictOpen U) :=
  ⟨(topologicalKrullDim_opens_eq hX U).trans hK.1, nonempty_restrict_smoothLocus_iso hK U⟩

/-- On a smooth scheme over `k`, the divisorial sheaf of a canonical divisor of dimension `n` is
`Ω^n`. -/
private theorem nonempty_divisorialSheaf_iso_of_isCanonicalDivisor' {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ Spec (.of k)} (hf : IsSmoothScheme f) {n : ℕ}
    {K : Divisor Y} (hK : K.IsCanonicalDivisor f n) :
    Nonempty (K.divisorialSheaf ≅ Scheme.Hom.relativeDifferentialForms f n) := by
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso (smoothLocus f).ι f _ rfl n
  exact MMP.Flips.nonempty_iso_of_restrict_iso hf (hK.iso ≪≫ e₁.symm)

end OpenRestriction

/-! ### Adjunction for a smooth effective Cartier divisor -/

section Adjunction

/-- **The quotient of a short exact sequence of finite locally free modules has the complementary
constant rank.** If `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` is short exact, `ℱ₁` has rank `a`, `ℱ₂` has rank
`a + c` and `ℱ₃` is finite locally free, then `ℱ₃` has rank `c`. -/
private theorem isFiniteLocallyFreeOfRank_X₃_of_shortExact {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (a c : ℕ)
    (h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ a)
    (h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (a + c))
    (h₃ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ c := by
  choose U hx r hr using fun x : X ↦
    Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict S.X₃ h₃ x
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₃ c).mp ?_
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U ?_ fun x ↦ ?_
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨y, hx y⟩
  · let G := Scheme.Modules.restrictFunctor (U x).ι
    have hS' : (S.map G).ShortExact := hS.map_of_exact G
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₁ a :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₁ a).mpr h₁).restrict (U x).ι)
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₂ (a + c) :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₂ (a + c)).mpr h₂).restrict (U x).ι)
    have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₃ (r x) := hr x
    have hc : r x = c := by
      have := SheafOfModules.rank_add_of_shortExact (S.map G) hS' a (a + c) (r x)
        (⟨x, hx x⟩ : (U x).toScheme)
      omega
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr (hc ▸ hr x)

/-- **The determinant of a short exact sequence with a line subbundle** ([Stacks, Tag 0B38]):
for `0 ⟶ ℱ ⟶ ℰ ⟶ ℒ ⟶ 0` short exact with `ℱ` of rank one and `ℒ` of rank `m + 1`,
`⋀¹ ℱ ⊗ ⋀^{m+1} ℒ ≅ ⋀^{m+2} ℰ`. -/
private theorem nonempty_tensor_exteriorPower_iso {X : Scheme.{u}} {F E L : X.Modules}
    (i : F ⟶ E) (q : E ⟶ L) (w : i ≫ q = 0) (hS : (ShortComplex.mk i q w).ShortExact) (m : ℕ)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 1]
    [hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L (m + 1)] :
    Nonempty (Scheme.Modules.exteriorPower F ((1 : ℕ) : ℤ) ⊗
        Scheme.Modules.exteriorPower L ((m + 1 : ℕ) : ℤ) ≅
      Scheme.Modules.exteriorPower E ((1 + (m + 1) : ℕ) : ℤ)) :=
  ⟨@asIso _ _ _ _ _ (@Stacks.SheafOfModules.TopWedge.isIso_detComparison _ X.sheaf F E L
    (_root_.SheafOfModules.algebras _ F) (_root_.SheafOfModules.algebras _ E)
    (_root_.SheafOfModules.algebras _ L) i q w hS.exact hS.mono_f hS.epi_g 1 m hF hL)⟩

/-- **Adjunction for a smooth effective Cartier divisor.** Let `Y` be separated and smooth of
relative dimension `n + 1` over a field `k`, and `T = V(I) ⊆ Y` an effective Cartier divisor,
smooth over `k`, with closed immersion `i : T ⟶ Y`. Then `i^*(Ω^{n+1}_{Y/k} ⊗ 𝒪_Y(T)) ≅ Ω^n_{T/k}`.

The conormal sheaf of `T` is `i^* ℐ_T = i^* 𝒪_Y(-T)`, so the conormal sequence
`0 ⟶ 𝒞_{T/Y} ⟶ i^*Ω_{Y/k} ⟶ Ω_{T/k} ⟶ 0` gives, taking determinants,
`i^*Ω^{n+1}_{Y/k} ≅ i^*𝒪_Y(-T) ⊗ Ω^n_{T/k}`. -/
private theorem nonempty_pullback_canonical_twist_iso_invertibleSheaf
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsSeparated sY] {n : ℕ} [SmoothOfRelativeDimension (n + 1) sY]
    (I : Y.IdealSheafData) [hI : Stacks.Divisors.IsEffectiveCartierDivisor I]
    [Smooth (I.subschemeι ≫ sY)] :
    Nonempty ((Scheme.Modules.pullback I.subschemeι).obj
        (Scheme.Hom.relativeDifferentialForms sY (n + 1) ⊗
          (show Y.Modules from Stacks.Divisors.invertibleSheaf' I)) ≅
      Scheme.Hom.relativeDifferentialForms (I.subschemeι ≫ sY) n) := by
  classical
  let i := I.subschemeι
  let N : Y.Modules := Stacks.Divisors.negativeTwist' I
  let Linv : Y.Modules := Stacks.Divisors.invertibleSheaf' I
  let S := Stacks.ConormalSequenceRight.conormalShortComplex i sY
  have hS : S.ShortExact :=
    Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i sY inferInstance
  -- the conormal sheaf is `i^* ℐ`
  let eC : S.X₁ ≅ (Scheme.Modules.pullback i).obj N :=
    (RingedSpaceModuleAdjunction.modulePullback i.liftCoborder.toLRSHom.toShHom).mapIso
      (Stacks.SheafOfModules.kernelIsoKerObj _).symm ≪≫
      Stacks.CartierConormal.conormalSheafIsoNegativeTwist I
  -- ranks
  have hNinv := Stacks.Divisors.isTensorInvertible_negativeTwist I
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1 :=
    (Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one Y N).1 hNinv
  have hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eC.symm
      (Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_obj i _ 1)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials sY) (n + 1) :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials sY (n + 1)
  have h₂ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (1 + n) := by
    rw [Nat.add_comm]
    exact Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_obj i _ (n + 1)
  have h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ n :=
    isFiniteLocallyFreeOfRank_X₃_of_shortExact S hS 1 n hC h₂
      (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials (i ≫ sY))
  -- `i^* Ω^{n+1}_{Y/k} ≅ 𝒞 ⊗ Ω^n_{T/k}`
  have key : Nonempty ((Scheme.Modules.pullback i).obj
      (Scheme.Hom.relativeDifferentialForms sY (n + 1)) ≅
      S.X₁ ⊗ Scheme.Hom.relativeDifferentialForms (i ≫ sY) n) := by
    have eP := Scheme.Modules.exteriorPowerPullbackIso i
      (Scheme.Hom.relativeDifferentials sY) ((n : ℤ) + 1)
    have g₁ := fun (M : I.subscheme.Modules) =>
      @asIso _ _ _ _ (Scheme.Modules.exteriorGenerator M)
        (SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_gen _ M
          (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra M))
    rcases n with _ | m
    · -- `Ω_T = 0`, so `𝒞 ≅ i^* Ω_Y`
      have hz : Limits.IsZero S.X₃ := Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRank_zero S.X₃
      have hg : S.g = 0 := hz.eq_of_tgt _ _
      have := hS.mono_f
      have : Epi S.f := hS.exact.epi_f hg
      have : IsIso S.f := isIso_of_mono_of_epi S.f
      refine ⟨eP ≪≫ eqToIso (by norm_num; rfl) ≪≫ (g₁ S.X₂).symm ≪≫ (asIso S.f).symm ≪≫
        (ρ_ _).symm ≪≫ whiskerLeftIso _
          ((Scheme.Hom.relativeDifferentialFormsZeroIso (i ≫ sY)).symm ≪≫
          eqToIso (by norm_num))⟩
    · obtain ⟨d⟩ := nonempty_tensor_exteriorPower_iso S.f S.g S.zero hS m
      refine ⟨eP ≪≫ eqToIso (by congr 1; push_cast; ring) ≪≫ d.symm ≪≫
        whiskerRightIso ((eqToIso (by norm_num)) ≪≫ (g₁ S.X₁).symm) _ ≪≫
        whiskerLeftIso _ (eqToIso (by push_cast; rfl))⟩
  -- `𝒞 ⊗ i^* 𝒪_Y(T) ≅ 𝒪_T`
  have hCL : Nonempty (S.X₁ ⊗ (Scheme.Modules.pullback i).obj Linv ≅
      𝟙_ I.subscheme.Modules) := by
    have e₀ : N ⊗ Linv ≅ 𝟙_ Y.Modules :=
      Stacks.SheafOfModules.Invertible.tensorProductBraiding _ _ N Linv ≪≫
        Stacks.SheafOfModules.Scheme.evaluationIso Y (Stacks.Divisors.negativeTwist' I)
    exact ⟨whiskerRightIso eC _ ≪≫
      (Stacks.RelativeVeryAmple.pullbackTensorModulesIso i _ _).symm ≪≫
      (Scheme.Modules.pullback i).mapIso e₀ ≪≫
      @asIso _ _ _ _ _
        (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{u} i.toRingCatSheafHom)⟩
  obtain ⟨e₁⟩ := key
  obtain ⟨e₂⟩ := hCL
  let β : Scheme.Hom.relativeDifferentialForms (i ≫ sY) n ⊗
      (Scheme.Modules.pullback i).obj Linv ≅
      (Scheme.Modules.pullback i).obj Linv ⊗
        Scheme.Hom.relativeDifferentialForms (i ≫ sY) n :=
    Stacks.SheafOfModules.Invertible.tensorProductBraiding I.subscheme.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf I.subscheme) _ _
  exact ⟨Stacks.RelativeVeryAmple.pullbackTensorModulesIso i _ _ ≪≫ whiskerRightIso e₁ _ ≪≫
    α_ _ _ _ ≪≫ whiskerLeftIso _ β ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso e₂ _ ≪≫ λ_ _⟩

/-- **Adjunction for the zero scheme of a section.** Let `Y` be an integral scheme, separated and
smooth of relative dimension `n + 1` over `k`, `M` an invertible `𝒪_Y`-module and `s ≠ 0` a
global section of `M` whose zero scheme `T = Z(s)` is smooth over `k`. Then
`i^*(Ω^{n+1}_{Y/k} ⊗ M) ≅ Ω^n_{T/k}`: indeed `M ≅ 𝒪_Y(T)`. -/
private theorem nonempty_pullback_canonical_twist_iso_zeroScheme {k : Type u} [Field k]
    {Y : Scheme.{u}} [IsIntegral Y] (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] {n : ℕ}
    [SmoothOfRelativeDimension (n + 1) sY] (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (s : Γ(M, ⊤)) (hs : s ≠ 0) [Smooth ((Stacks.Divisors.zeroScheme Y M s).subschemeι ≫ sY)] :
    Nonempty ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y M s).subschemeι).obj
        (Scheme.Hom.relativeDifferentialForms sY (n + 1) ⊗ M) ≅
      Scheme.Hom.relativeDifferentialForms
        ((Stacks.Divisors.zeroScheme Y M s).subschemeι ≫ sY) n) := by
  have := isEffectiveCartierDivisor_zeroScheme_of_ne_zero M s hs
  obtain ⟨e⟩ := nonempty_pullback_canonical_twist_iso_invertibleSheaf sY (n := n)
    (Stacks.Divisors.zeroScheme Y M s)
  exact ⟨(Scheme.Modules.pullback _).mapIso (whiskerLeftIso _
    (invertibleSheafIsoZeroScheme M s fun U r t h =>
      eq_of_smul_map_le_top_eq_of_isIntegral M s hs U h)) ≪≫ e⟩

end Adjunction

/-! ### Transversality -/

section Transversality

/-- Let `z₁, …, zₙ` be a regular system of parameters of a regular local ring `A` and
`ψ : A ⟶ B` a surjection onto a one-dimensional local domain with kernel `(z_a)`. Then the image
of any other `z_b` is a uniformizer of `B`: `B = A ⧸ (z_a)` has dimension `n - 1`, so `n = 2` and
the maximal ideal of `B` is generated by `ψ(z_b)`. -/
private theorem irreducible_map_of_isRegularSystemOfParameters {A B : Type*} [CommRing A]
    [IsRegularLocalRing A] [CommRing B] [IsDomain B] [IsLocalRing B] (ψ : A →+* B)
    (hψ : Function.Surjective ψ) {n : ℕ} {z : Fin n → A}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) {a b : Fin n} (hab : a ≠ b)
    (hker : RingHom.ker ψ = Ideal.span {z a}) (hB : ringKrullDim B = 1) :
    Irreducible (ψ (z b)) := by
  classical
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have hza : z a ∈ IsLocalRing.maximalIdeal A := hz.1 ▸ Ideal.subset_span ⟨a, rfl⟩
  have hza0 : z a ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz a
  -- `B ≅ A ⧸ (z_a)` has dimension `n - 1`
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hza0) hza
  rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hψ)), hB, hz.2] at hdim
  have hn : n = 2 := by
    have : ((1 : ℕ) : WithBot ℕ∞) + 1 = (n : WithBot ℕ∞) := by exact_mod_cast hdim
    have h2 : ((2 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [← this]; norm_num
    exact_mod_cast h2.symm
  subst hn
  have : IsLocalHom ψ := IsLocalHom.of_surjective ψ hψ
  have hmax : IsLocalRing.maximalIdeal B = Ideal.span {ψ (z b)} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective ψ hψ, ← hz.1, Ideal.map_span]
    have hza' : ψ (z a) = 0 := by
      rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rcases (show i = a ∨ i = b by omega) with rfl | rfl
      · rw [hza']; exact zero_mem _
      · exact Ideal.mem_span_singleton_self _
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨z b, ⟨b, rfl⟩, rfl⟩
  have hne : ψ (z b) ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at hmax
    have hfield := (IsLocalRing.isField_iff_maximalIdeal_eq).2 hmax
    rw [ringKrullDim_eq_zero_of_isField hfield] at hB
    exact absurd hB (by decide)
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hmax

/-- The kernel of the stalk map of a closed subscheme `V(I) ⟶ Y` precomposed with an open
immersion `φ : V ⟶ V(I)` is the stalk of `I`, and the map is surjective. -/
private theorem stalkMap_comp_subschemeι_surjective_and_ker {Y V : Scheme.{u}}
    (I : Y.IdealSheafData) (φ : V ⟶ I.subscheme) [IsOpenImmersion φ] (v : V) :
    Function.Surjective ((φ ≫ I.subschemeι).stalkMap v).hom ∧
      RingHom.ker ((φ ≫ I.subschemeι).stalkMap v).hom =
        IdealSheafData.stalk I ((φ ≫ I.subschemeι) v) := by
  have : IsIso (φ.stalkMap v) := @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ φ ‹_› v
  have hbij := ConcreteCategory.bijective_of_isIso (φ.stalkMap v)
  have h := Scheme.Hom.stalkMap_comp φ I.subschemeι v
  have happ : ∀ a, ((φ ≫ I.subschemeι).stalkMap v).hom a =
      (φ.stalkMap v).hom ((I.subschemeι.stalkMap (φ v)).hom a) := fun a => by
    rw [h]; rfl
  refine ⟨fun b => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hbij.2 b
    obtain ⟨c, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective I.subschemeι (φ v) a
    exact ⟨c, happ c⟩
  · ext a
    rw [RingHom.mem_ker, happ, map_eq_zero_iff _ hbij.1]
    change a ∈ RingHom.ker (I.subschemeι.stalkMap (φ v)).hom ↔
      a ∈ IdealSheafData.stalk I (I.subschemeι (φ v))
    rw [Scheme.IdealSheafData.ker_stalkMap_subschemeι, stalk_eq_stalkIdeal]

open Classical in
/-- **Transversality and multiplicity one.** Let `Y` be a smooth variety, `I` an ideal sheaf
on `Y` and `(Gₗ)` ideal sheaves with `V(I) + ∑ V(Gₗ)` a simple normal crossing family, `E` a
prime divisor of `Y` with `I_E = G_l`, and `κ : V ⟶ Y` the composite of an open immersion
`V ⟶ V(I)` and `V(I) ⟶ Y`, with `V` normal and the generic points of `V` off `E`. Then the
pull-back of `E` to `V` has coefficient `1` along each prime divisor of `V` lying over `E`, and
`0` along the others: at `y = κ(η_P)` the local ring of `V` is `𝒪_{Y,y} ⧸ (z_a)`, of dimension
one, so `E = (z_b = 0)` restricts to a uniformizer. -/
private theorem exists_ordUnit_pullbackComponent_single {k : Type u} [Field k]
    {Y V : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [hY : IsSmoothVariety k sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian V] [IsNormal V]
    (I : Y.IdealSheafData) {Λ : Type*} (G : Λ → Y.IdealSheafData)
    (hsnc : MMP.Resolution.IsSNCFamily sY (fun o : Option Λ => o.elim I G))
    (φ : V ⟶ I.subscheme) [IsOpenImmersion φ]
    (E : MMP.Mori.PrimeDivisor Y) (l : Λ) (hl : G l = E.idealSheaf)
    (hB : ∀ Z : irreducibleComponents V,
      (φ ≫ I.subschemeι) (componentGenericPoint V Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single E (1 : ℤ)))
    (P : MMP.Mori.PrimeDivisor V) :
    ∃ (U : Y.Opens) (ψ : (RationalFunctions Y)ˣ)
      (hψ : Divisor.IsLocalEquation (Finsupp.single E 1) U ψ)
      (hP : (P.support ∩ (φ ≫ I.subschemeι) ⁻¹ᵁ U).Nonempty),
      P.ordUnit (pullbackComponent (φ ≫ I.subschemeι) hB hψ P.component
        (P.map_componentGenericPoint_mem _ hP)) =
        if (φ ≫ I.subschemeι) P.genericPoint ∈ E.support then 1 else 0 := by
  classical
  set κ := φ ≫ I.subschemeι with hκ
  have hPgen : P.genericPoint ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  by_cases hy : κ P.genericPoint ∈ E.support
  · rw [ite_eq_left hy]
    obtain ⟨-, hloc, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY
    obtain ⟨U, hyU, g, ψ, hψg, hψ, hgI⟩ := hloc E (κ P.genericPoint)
    have hP : (P.support ∩ κ ⁻¹ᵁ U).Nonempty := ⟨P.genericPoint, hPgen, hyU⟩
    refine ⟨U, ψ, hψ, hP, ?_⟩
    set ηV := componentGenericPoint V P.component
    have hηVU : κ ηV ∈ (U : Y.Opens) := P.map_componentGenericPoint_mem κ hP
    -- `κ(η_V)` is off `E`, so the local equation `g` is a unit there
    have hηE : κ ηV ∉ E.support := fun h => hB P.component
      (DivisorWithCoeffs.mem_supp_iff.2 ⟨E, by simp [DivisorWithCoeffs.coeff], h⟩)
    have hstalk : ∀ (x : Y) (hx : x ∈ (U : Y.Opens)),
        IdealSheafData.stalk E.idealSheaf x = Ideal.span {Y.presheaf.germ U x hx g} := by
      intro x hx
      rw [IdealSheafData.stalk_eq_map_germ E.idealSheaf x U hx, hgI, Ideal.map_span,
        Set.image_singleton]
    have hunit : IsUnit (Y.presheaf.germ U (κ ηV) hηVU g) := by
      rw [← Ideal.span_singleton_eq_top, ← hstalk]
      by_contra hne
      exact hηE ((Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support _ _).1
        (IsLocalRing.le_maximalIdeal hne))
    have hW := mem_pointComponent (κ ηV)
    have hcgp : componentGenericPoint Y (pointComponent (κ ηV)) ∈ (U : Y.Opens) :=
      ((isGenericPoint_componentGenericPoint Y _).specializes hW).mem_open U.1.isOpen hηVU
    have ha : (stalkToRationalFunctions Y hW).hom (hunit.unit : Y.presheaf.stalk (κ ηV)) =
        (ψ : RationalFunctions Y) (pointComponent (κ ηV)) := by
      rw [hψg _ hcgp, IsUnit.unit_spec]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [pullbackComponent_eq hB hψ hηVU hW hunit.unit ha]
    -- the image of `g` in `𝒪_{V,P}` is a uniformizer
    set b : V.presheaf.stalk P.genericPoint :=
      (κ.stalkMap P.genericPoint).hom (Y.presheaf.germ U (κ P.genericPoint) hyU g) with hb
    have hval : ((Units.map (κ.stalkMap ηV).hom.toMonoidHom hunit.unit :
        (V.presheaf.stalk ηV)ˣ) : V.presheaf.stalk ηV) = P.toComponent.hom b := by
      change (κ.stalkMap ηV).hom (Y.presheaf.germ U (κ ηV) hηVU g) =
        (V.presheaf.stalkSpecializes _).hom
          ((κ.stalkMap P.genericPoint).hom (Y.presheaf.germ U _ hyU g))
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
      exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
    have hirr : Irreducible b := by
      have : Smooth sY := hY.toSmooth
      have := isRegularLocalRing_stalk_of_smooth_over_field sY (κ P.genericPoint)
      have hyI : κ P.genericPoint ∈ (I.support : Set Y) := by
        rw [← I.range_subschemeι]; exact ⟨φ P.genericPoint, rfl⟩
      obtain ⟨n, z, c, hz, hc, hinj⟩ := hsnc.2 (κ P.genericPoint)
      let iI : {o : Option Λ // κ P.genericPoint ∈ (o.elim I G).support} := ⟨none, hyI⟩
      let iE : {o : Option Λ // κ P.genericPoint ∈ (o.elim I G).support} :=
        ⟨some l, by change _ ∈ (G l).support; rw [hl]; exact hy⟩
      have hab : c iI ≠ c iE := fun h => by
        have := congrArg Subtype.val (hinj h)
        simp [iI, iE] at this
      obtain ⟨hsurj, hker⟩ := stalkMap_comp_subschemeι_surjective_and_ker I φ P.genericPoint
      have hker' : RingHom.ker (κ.stalkMap P.genericPoint).hom = Ideal.span {z (c iI)} :=
        hker.trans (hc iI)
      have hdim : ringKrullDim (V.presheaf.stalk P.genericPoint) = 1 := by
        rw [ringKrullDim_stalk_eq_coheight, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
        rfl
      have h1 := irreducible_map_of_isRegularSystemOfParameters (κ.stalkMap P.genericPoint).hom
        hsurj hz hab hker' hdim
      have hass : Associated (Y.presheaf.germ U (κ P.genericPoint) hyU g) (z (c iE)) := by
        have : IsDomain (Y.presheaf.stalk (κ P.genericPoint)) := IsRegularLocalRing.isDomain _
        rw [← Ideal.span_singleton_eq_span_singleton, ← hstalk, ← hl]
        exact hc iE
      exact (hass.map (κ.stalkMap P.genericPoint).hom).irreducible_iff.2 h1
    have h := P.valuation_eq_exp_ordUnit (Units.map (κ.stalkMap ηV).hom.toMonoidHom hunit.unit)
    rw [hval, P.valuation_toComponent_of_irreducible hirr] at h
    exact (WithZero.exp_inj.1 h).symm
  · rw [ite_eq_right hy]
    let U : Y.Opens := ⟨(E.support : Set Y)ᶜ, E.idealSheaf.support.isClosed.isOpen_compl⟩
    have h1 : Divisor.IsLocalEquation (Finsupp.single E 1) U 1 := by
      intro E' hE'
      rw [PrimeDivisor.ord_one]
      by_cases hEE : E' = E
      · subst hEE
        obtain ⟨x, hx, hxU⟩ := hE'
        exact absurd hx hxU
      · simp [DivisorWithCoeffs.coeff, Ne.symm hEE]
    have hP : (P.support ∩ κ ⁻¹ᵁ U).Nonempty := ⟨P.genericPoint, hPgen, hy⟩
    refine ⟨U, 1, h1, hP, ?_⟩
    have hW := mem_pointComponent (κ (componentGenericPoint V P.component))
    rw [pullbackComponent_eq hB h1 (P.map_componentGenericPoint_mem _ hP) hW 1 (by simp),
      map_one, PrimeDivisor.ordUnit_one]

open Classical in
/-- The coefficients of the pull-back of a single snc component. -/
private theorem coeff_pullback_single {k : Type u} [Field k]
    {Y V : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothVariety k sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (I : Y.IdealSheafData) {Λ : Type*} (G : Λ → Y.IdealSheafData)
    (hsnc : MMP.Resolution.IsSNCFamily sY (fun o : Option Λ => o.elim I G))
    (φ : V ⟶ I.subscheme) [IsOpenImmersion φ]
    (E : MMP.Mori.PrimeDivisor Y) (l : Λ) (hl : G l = E.idealSheaf)
    (hEc : Divisor.IsCartier (Finsupp.single E (1 : ℤ)))
    (hB : ∀ Z : irreducibleComponents V,
      (φ ≫ I.subschemeι) (componentGenericPoint V Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single E (1 : ℤ)))
    (P : MMP.Mori.PrimeDivisor V) :
    (Divisor.pullback (f := φ ≫ I.subschemeι) (Finsupp.single E (1 : ℤ)) hEc hB).coeff P =
      if (φ ≫ I.subschemeι) P.genericPoint ∈ E.support then 1 else 0 := by
  obtain ⟨U, ψ, hψ, hP, h⟩ :=
    exists_ordUnit_pullbackComponent_single sY I G hsnc φ E l hl hB P
  rw [Divisor.isPullback_pullback hEc hB U ψ hψ P hP, h]

open Classical in
/-- **The pull-back of a divisor supported on the snc components.** With the notation of
`exists_ordUnit_pullbackComponent_single`, a divisor `B₀ = ∑ b_E E` whose components are among
the `V(Gₗ)` pulls back to `V` with coefficient `∑_{E ∋ κ(η_P)} b_E` along `P`. -/
private theorem exists_isPullback_of_support_subset {k : Type u} [Field k]
    {Y V : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothVariety k sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (I : Y.IdealSheafData) {Λ : Type*} (G : Λ → Y.IdealSheafData)
    (hsnc : MMP.Resolution.IsSNCFamily sY (fun o : Option Λ => o.elim I G))
    (φ : V ⟶ I.subscheme) [IsOpenImmersion φ] (hYc : ∀ D : Divisor Y, D.IsCartier)
    (B₀ : Divisor Y) (hB₀ : ∀ E ∈ B₀.support, ∃ l, G l = E.idealSheaf)
    (hB : ∀ Z : irreducibleComponents V,
      (φ ≫ I.subschemeι) (componentGenericPoint V Z) ∉ B₀.supp) :
    ∃ B' : Divisor V, B₀.IsPullback (φ ≫ I.subschemeι) hB B' ∧
      ∀ P : MMP.Mori.PrimeDivisor V, B'.coeff P = ∑ E ∈ B₀.support,
        B₀.coeff E * if (φ ≫ I.subschemeι) P.genericPoint ∈ E.support then 1 else 0 := by
  set κ := φ ≫ I.subschemeι with hκ
  -- `(∗)` for the partial sums
  have hsuppS : ∀ S ⊆ B₀.support, ∀ Z : irreducibleComponents V, κ (componentGenericPoint V Z) ∉
      DivisorWithCoeffs.supp (∑ E ∈ S, B₀.coeff E • Finsupp.single E (1 : ℤ)) := by
    intro S hS Z hmem
    obtain ⟨E', hE'c, hE'⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
    have hE'S : E' ∈ S := by
      by_contra hn
      apply hE'c
      simp only [DivisorWithCoeffs.coeff, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      refine Finset.sum_eq_zero fun E hE => ?_
      rw [ite_eq_right]
      rintro rfl
      exact hn hE
    exact hB Z (DivisorWithCoeffs.mem_supp_iff.2
      ⟨E', Finsupp.mem_support_iff.1 (hS hE'S), hE'⟩)
  have hsingle : ∀ E ∈ B₀.support, ∀ Z : irreducibleComponents V,
      κ (componentGenericPoint V Z) ∉ DivisorWithCoeffs.supp (Finsupp.single E (1 : ℤ)) := by
    intro E hE Z hmem
    obtain ⟨E', hE'c, hE'⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
    have : E' = E := by
      by_contra hn
      exact hE'c (by simp [DivisorWithCoeffs.coeff, Ne.symm hn])
    subst this
    exact hB Z (DivisorWithCoeffs.mem_supp_iff.2 ⟨E', Finsupp.mem_support_iff.1 hE, hE'⟩)
  have key : ∀ (S : Finset (MMP.Mori.PrimeDivisor Y)) (hS : S ⊆ B₀.support), ∃ B' : Divisor V,
      Divisor.IsPullback κ (∑ E ∈ S, B₀.coeff E • Finsupp.single E (1 : ℤ)) (hsuppS S hS) B' ∧
      ∀ P : MMP.Mori.PrimeDivisor V, B'.coeff P = ∑ E ∈ S,
        B₀.coeff E * if κ P.genericPoint ∈ E.support then 1 else 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro hS
      refine ⟨0, Divisor.IsPullback.of_eq (by simp) (Divisor.isPullback_zero (f := κ)
        (fun Z h => by
          obtain ⟨E', hE'c, -⟩ := DivisorWithCoeffs.mem_supp_iff.1 h
          exact hE'c (DivisorWithCoeffs.coeff_zero E'))), fun P => by
        simp [DivisorWithCoeffs.coeff_zero]⟩
    | insert a S ha ih =>
      intro hS
      obtain ⟨B', hB', hc⟩ := ih ((Finset.subset_insert a S).trans hS)
      have haB : a ∈ B₀.support := hS (Finset.mem_insert_self a S)
      obtain ⟨l, hl⟩ := hB₀ a haB
      have hFa := Divisor.isPullback_pullback (f := κ) (hYc _) (hsingle a haB)
      have h2 := hFa.zsmul (hYc _) (B₀.coeff a) (fun Z hmem =>
        hsuppS {a} (by simpa using haB) Z (by simpa using hmem))
      refine ⟨B₀.coeff a • Divisor.pullback (f := κ) (Finsupp.single a (1 : ℤ)) (hYc _)
        (hsingle a haB) + B', ?_, fun P => ?_⟩
      · have hB1 : ∀ Z : irreducibleComponents V, κ (componentGenericPoint V Z) ∉
            DivisorWithCoeffs.supp (B₀.coeff a • Finsupp.single a (1 : ℤ) +
              ∑ x ∈ S, B₀.coeff x • Finsupp.single x (1 : ℤ)) := fun Z h =>
          hsuppS (insert a S) hS Z (by rwa [Finset.sum_insert ha])
        exact Divisor.IsPullback.of_eq (hB₁ := hB1) (Finset.sum_insert ha).symm
          (Divisor.IsPullback.add (hYc _) (hYc _) hB1 h2 hB')
      · rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
          coeff_pullback_single sY I G hsnc φ a l hl (hYc _) (hsingle a haB) P, hc P,
          Finset.sum_insert ha, smul_eq_mul]
  obtain ⟨B', hB', hc⟩ := key B₀.support le_rfl
  refine ⟨B', Divisor.IsPullback.of_eq ?_ hB', hc⟩
  conv_rhs => rw [← Finsupp.sum_single B₀]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

end Transversality

/-! ### Tensor powers -/

section TensorPow

open MMP.Intersection.Scheme.Modules (tensorPow)

/-- The braiding of the tensor product of `𝒪_X`-modules. -/
private noncomputable def braidModules {X : Scheme.{u}} (A B : X.Modules) : A ⊗ B ≅ B ⊗ A :=
  Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) A B

/-- The middle-four interchange `(P ⊗ Q) ⊗ (R ⊗ S) ≅ (P ⊗ R) ⊗ (Q ⊗ S)`. -/
private noncomputable def tensorTensorTensorComm {X : Scheme.{u}} (P Q R S : X.Modules) :
    (P ⊗ Q) ⊗ (R ⊗ S) ≅ (P ⊗ R) ⊗ (Q ⊗ S) :=
  α_ P Q (R ⊗ S) ≪≫ whiskerLeftIso P ((α_ Q R S).symm ≪≫ whiskerRightIso (braidModules Q R) S ≪≫
    α_ R Q S) ≪≫ (α_ P R (Q ⊗ S)).symm

/-- Tensor powers are functorial in isomorphisms. -/
private theorem nonempty_tensorPow_congr {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B)
    (m : ℕ) : Nonempty (tensorPow A m ≅ tensorPow B m) := by
  induction m with
  | zero => exact ⟨Iso.refl _⟩
  | succ m ih =>
    obtain ⟨e'⟩ := ih
    exact ⟨whiskerRightIso e' A ≪≫ whiskerLeftIso _ e⟩

/-- `(A ⊗ B)^{⊗ m} ≅ A^{⊗ m} ⊗ B^{⊗ m}`. -/
private theorem nonempty_tensorPow_tensor_iso {X : Scheme.{u}} (A B : X.Modules) (m : ℕ) :
    Nonempty (tensorPow (A ⊗ B) m ≅ tensorPow A m ⊗ tensorPow B m) := by
  induction m with
  | zero => exact ⟨(λ_ (𝟙_ X.Modules)).symm⟩
  | succ m ih =>
    obtain ⟨e⟩ := ih
    exact ⟨whiskerRightIso e (A ⊗ B) ≪≫ tensorTensorTensorComm _ _ _ _⟩

/-- Pull-back commutes with tensor powers. -/
private theorem nonempty_pullback_tensorPow_iso {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (m : ℕ) : Nonempty ((Scheme.Modules.pullback f).obj (tensorPow M m) ≅
      tensorPow ((Scheme.Modules.pullback f).obj M) m) := by
  induction m with
  | zero =>
    exact ⟨@asIso _ _ _ _ _
      (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{u} f.toRingCatSheafHom)⟩
  | succ m ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Stacks.RelativeVeryAmple.pullbackTensorModulesIso f _ _ ≪≫ whiskerRightIso e _⟩

/-- For Cartier divisors `A`, `B`: `𝒪(mA + B) ≅ 𝒪(A)^{⊗ m} ⊗ 𝒪(B)`. -/
public theorem Divisor.IsCartier.nonempty_divisorialSheaf_zsmul_add_iso {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {A B : Divisor Y} (hA : A.IsCartier)
    (hB : B.IsCartier) (m : ℕ) : Nonempty (((m : ℤ) • A + B).divisorialSheaf ≅
      tensorPow A.divisorialSheaf m ⊗ B.divisorialSheaf) := by
  induction m with
  | zero => exact ⟨eqToIso (by simp) ≪≫ (λ_ _).symm⟩
  | succ m ih =>
    obtain ⟨e⟩ := ih
    have hmB : ((m : ℤ) • A + B).IsCartier := (hA.zsmul m).add hB
    have heq : (((m + 1 : ℕ) : ℤ) • A + B) = A + ((m : ℤ) • A + B) := by
      push_cast; rw [add_smul, one_smul]; abel
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf heq) ≪≫
      (Divisor.IsCartier.divisorialSheafTensorIso hA hmB).symm ≪≫ whiskerLeftIso _ e ≪≫
      (α_ _ _ _).symm ≪≫ whiskerRightIso (braidModules _ _) _⟩

end TensorPow

/-! ### Invertible sheaves -/

section Invertible

open MMP.Intersection.Scheme.Modules (tensorPow)

/-- Tensor powers of an invertible module are invertible. -/
private theorem isInvertibleModule_tensorPow {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (m : ℕ) :
    Stacks.Ample.IsInvertibleModule X (tensorPow L m) := by
  induction m with
  | zero => exact Stacks.Ample.isInvertibleModule_unit X
  | succ m ih =>
    have := ih
    exact Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X (tensorPow L m) L

/-- On an integral, locally Noetherian, normal, quasi-compact scheme every invertible module is
`𝒪(D)` for a Cartier divisor `D`: the divisor of a local frame has the inverse transition
functions as local equations. -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    ∃ D : MMP.Mori.Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
    (h := ‹_›)
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    Y.isLocalRing
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : MMP.Mori.LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := ha, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

end Invertible

/-! ### The main step, for a fixed general member -/

section Member

attribute [local instance] globalSectionsModule

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-- The coefficient identity `m K' + B|_S = m (K' + Δ|_S)` for the restriction by components of
a boundary `B = m Δ` along a morphism `j : S ⟶ Y` of pure codimension one avoiding `Supp Δ`. -/
private theorem toQDivisor_zsmul_add_restrictComponents {Y S : Scheme.{u}} [NoetherianSpace S]
    (j : S ⟶ Y) (hpure : ∀ s : S, Order.coheight s = 0 → Order.coheight (j s) = 1)
    {Δ : QDivisor Y} (havoid : ∀ E ∈ Δ.support, E.genericPoint ∉ Set.range j)
    (m : ℕ) (K' : Divisor S) {B : Divisor Y} (hBcoeff : ∀ E, (B.coeff E : ℚ) = m * Δ.coeff E)
    (hBsupp : ∀ E ∈ B.support, E ∈ Δ.support) :
    Divisor.toQDivisor ((m : ℤ) • K' + B.restrictComponents j) =
      (m : ℤ) • (Divisor.toQDivisor K' + Δ.restrictComponents j) := by
  classical
  ext C
  have hcB := DivisorWithCoeffs.coeff_restrictComponents_of_pure j B hpure
    (fun E hE => havoid E (hBsupp E hE)) C
  have hcΔ := DivisorWithCoeffs.coeff_restrictComponents_of_pure j Δ hpure havoid C
  rw [Divisor.coeff_toQDivisor]
  simp only [DivisorWithCoeffs.coeff] at hcB hcΔ hBcoeff ⊢
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul,
    zsmul_eq_mul, Int.cast_natCast, hcB, hcΔ, mul_add]
  have hK'C : (Divisor.toQDivisor K') C = (K' C : ℚ) := rfl
  rw [hK'C]
  congr 1
  unfold Finsupp.sum
  push_cast
  rw [Finset.mul_sum, Finset.sum_subset (fun E hE => hBsupp E hE) (fun E _ hEB => by
    rw [Finsupp.notMem_support_iff.1 hEB]; simp)]
  refine Finset.sum_congr rfl fun E _ => ?_
  split_ifs
  · exact hBcoeff E
  · simp

/-- The adjunction statement on one connected component `W` of the member `Z(σ)`. -/
private theorem adjunction_step [IsAlgClosed k] [CharZero k] [IsLocallyNoetherian X] [IsNormal X]
    {Δ : QDivisor X} (hΔ : IsPair (X ↘ Spec (.of k)) Δ)
    (X₀ : X.Opens) (hX₀sm : X₀ ≤ smoothLocus (X ↘ Spec (.of k)))
    (hX₀ : ∀ x : X, Order.coheight x ≤ 1 → x ∈ X₀)
    (σ : Γ(L, ⊤))
    (havoidC : ∀ Y ∈ MMP.Resolution.componentsOf ((X₀ : Set X)ᶜ),
      (Y ∩ nonvanishingOpen X L σ).Nonempty)
    (hsnc : MMP.Resolution.IsSNCFamily (X₀.ι ≫ X ↘ Spec (.of k))
      (fun o : Option (Δ.restrictOpen X₀).support =>
        o.elim ((Stacks.Divisors.zeroScheme X L σ).comap X₀.ι) fun E => E.1.idealSheaf))
    (W : (Stacks.Divisors.zeroScheme X L σ).subscheme.Opens) [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral W] [CompactSpace W]
    (hWcl : IsClosed (W : Set (Stacks.Divisors.zeroScheme X L σ).subscheme))
    (hWvar : IsNormalVariety k
      (W.ι ≫ (Stacks.Divisors.zeroScheme X L σ).subschemeι ≫ X ↘ Spec (.of k)))
    (hcoh : ∀ w : W.toScheme,
      Order.coheight ((W.ι ≫ (Stacks.Divisors.zeroScheme X L σ).subschemeι) w) =
        Order.coheight w + 1)
    (havoid : ∀ E ∈ Δ.support, E.genericPoint ∉
      Set.range (W.ι ≫ (Stacks.Divisors.zeroScheme X L σ).subschemeι))
    (m : ℕ) (n n' : ℕ) (K : Divisor X) (K' : Divisor W.toScheme)
    (hK : K.IsCanonicalDivisor (X ↘ Spec (.of k)) n)
    (hK' : K'.IsCanonicalDivisor
      (W.ι ≫ (Stacks.Divisors.zeroScheme X L σ).subschemeι ≫ X ↘ Spec (.of k)) n')
    (D : Divisor X) (hD : Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor K + Δ))
    (hDc : D.IsCartier) :
    ∃ D' : Divisor W.toScheme,
      Divisor.toQDivisor D' = (m : ℤ) • (Divisor.toQDivisor K' +
        Δ.restrictComponents (W.ι ≫ (Stacks.Divisors.zeroScheme X L σ).subschemeι)) ∧
      D'.IsCartier ∧
      Nonempty (D'.divisorialSheaf ≅ (Scheme.Modules.pullback
        (W.ι ≫ (Stacks.Divisors.zeroScheme X L σ).subschemeι)).obj
          (D.divisorialSheaf ⊗ MMP.Intersection.Scheme.Modules.tensorPow L m)) := by
  classical
  have hX := hΔ.1
  have : AlgebraicGeometry.IsVariety k (X ↘ Spec (.of k)) := hX.1
  have : IsIntegral X := hX.1.toIsIntegral
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  let Z := Stacks.Divisors.zeroScheme X L σ
  have : IsLocallyNoetherian Z.subscheme := LocallyOfFiniteType.isLocallyNoetherian Z.subschemeι
  have : IsNoetherian W := ⟨⟩
  let j : W.toScheme ⟶ X := W.ι ≫ Z.subschemeι
  have hpure : ∀ w : W.toScheme, Order.coheight w = 0 → Order.coheight (j w) = 1 := by
    intro w hw
    rw [hcoh, hw, zero_add]
  have hηW : Order.coheight (j (genericPoint W)) = 1 := hpure _ (coheight_genericPoint_eq_zero W)
  have hηWE : ∀ E ∈ Δ.support, j (genericPoint W) ∉ E.support := fun E hE hmem =>
    havoid E hE ⟨genericPoint W,
      eq_genericPoint_of_mem_support_of_coheight_le_one hηW.le hmem⟩
  set B : Divisor X := D - (m : ℤ) • K with hBdef
  have hB : Divisor.toQDivisor B = (m : ℤ) • Δ := by
    rw [hBdef, map_sub, map_zsmul, hD, smul_add, add_sub_cancel_left]
  have hBcoeff : ∀ E, (B.coeff E : ℚ) = m * Δ.coeff E := fun E => by
    rw [← Divisor.coeff_toQDivisor, hB]
    simp [DivisorWithCoeffs.coeff]
  have hBsupp : ∀ E ∈ B.support, E ∈ Δ.support := fun E hE => by
    rw [Finsupp.mem_support_iff] at hE ⊢
    intro h0
    apply hE
    have := hBcoeff E
    rw [show Δ.coeff E = 0 from h0, mul_zero] at this
    exact_mod_cast this
  set D' : Divisor W := (m : ℤ) • K' + B.restrictComponents j with hD'def
  have hD'eq : Divisor.toQDivisor D' =
      (m : ℤ) • (Divisor.toQDivisor K' + Δ.restrictComponents j) :=
    toQDivisor_zsmul_add_restrictComponents j hpure havoid m K' hBcoeff hBsupp
  -- `𝒪_X(D) ⊗ L^m` pulls back to the divisorial sheaf of a Cartier divisor `E₀` of `W`
  have : Stacks.Ample.IsInvertibleModule X D.divisorialSheaf :=
    MMP.Mori.Divisor.IsCartier.isInvertibleModule_divisorialSheaf hDc
  have := isInvertibleModule_tensorPow L m
  have : Stacks.Ample.IsInvertibleModule X
      (D.divisorialSheaf ⊗ MMP.Intersection.Scheme.Modules.tensorPow L m) :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules X D.divisorialSheaf
      (MMP.Intersection.Scheme.Modules.tensorPow L m)
  have : Stacks.Ample.IsInvertibleModule W.toScheme ((Scheme.Modules.pullback j).obj
      (D.divisorialSheaf ⊗ MMP.Intersection.Scheme.Modules.tensorPow L m)) :=
    MMP.Fourfold.isInvertibleModule_pullback j _
  obtain ⟨E₀, hE₀c, ⟨eE₀⟩⟩ := exists_isCartier_divisorialSheaf_iso ((Scheme.Modules.pullback j).obj
      (D.divisorialSheaf ⊗ MMP.Intersection.Scheme.Modules.tensorPow L m))
  -- the open `V = W ∩ X°` contains every point of codimension one of `W`
  let V : W.toScheme.Opens := j ⁻¹ᵁ X₀
  have hV : ∀ Γ : MMP.Mori.PrimeDivisor W.toScheme, Γ.genericPoint ∈ V := fun Γ =>
    mem_of_coheight_le_two X₀ (nonvanishingOpen X L σ) hX₀ havoidC
      (by rw [hcoh, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; rfl)
      fun h => notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen L σ h
        (Z.mem_supportSet_iff_mem_support.2 (by
          change _ ∈ (Z.support : Set X); rw [← Z.range_subschemeι]; exact ⟨W.ι _, rfl⟩))
  -- adjunction on `V`
  obtain ⟨eV⟩ : Nonempty (D'.divisorialSheaf.restrict V.ι ≅ ((Scheme.Modules.pullback j).obj
      (D.divisorialSheaf ⊗ MMP.Intersection.Scheme.Modules.tensorPow L m)).restrict V.ι) := by
    -- the smooth variety `X°`
    let sY : X₀.toScheme ⟶ Spec (.of k) := X₀.ι ≫ X ↘ Spec (.of k)
    have hηWX₀ : j (genericPoint W) ∈ X₀ := hX₀ _ hηW.le
    have : Nonempty X₀ := ⟨⟨_, hηWX₀⟩⟩
    have : IsDominant X₀.ι := isDominant_opens_ι X₀
    have hYvar : IsNormalVariety k sY := isNormalVariety_ι hX X₀
    have : AlgebraicGeometry.IsVariety k sY := hYvar.1
    have : IsIntegral X₀.toScheme := hYvar.1.toIsIntegral
    have hsmY : Smooth sY := smooth_ι_comp_of_le_smoothLocus X₀ hX₀sm
    have : IsSmoothVariety k sY := (isSmoothVariety_iff k sY).2 ⟨inferInstance, hsmY⟩
    have : CompactSpace X₀.toScheme := QuasiCompact.compactSpace_of_compactSpace sY
    have hYc : ∀ D : Divisor X₀.toScheme, D.IsCartier :=
      (Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY).1
    have hdimY : topologicalKrullDim X₀.toScheme = n :=
      (topologicalKrullDim_opens_eq hX X₀).trans hK.1
    -- `n = n' + 1`
    have hnn : n = n' + 1 := eq_add_one_of_coheight_genericPoint_eq_one (X ↘ Spec (.of k)) j
      (Z.subschemeι.isClosedEmbedding.comp hWcl.isClosedEmbedding_subtypeVal) hηW hK.1 hK'.1
    have : SmoothOfRelativeDimension (n' + 1) sY :=
      hnn ▸ MMP.Intersection.smoothOfRelativeDimension_of_isVariety sY n hdimY
    -- the member on `X°`
    let I₀ := Z.comap X₀.ι
    let L₀ : X₀.toScheme.Modules := (Scheme.Modules.pullback X₀.ι).obj L
    have : Stacks.Ample.IsInvertibleModule X₀.toScheme L₀ :=
      MMP.Fourfold.isInvertibleModule_pullback X₀.ι L
    have : SheafOfModules.IsInvertible X₀.toScheme.sheaf.obj X₀.toScheme.ringCatSheaf.property
        L₀ := (inferInstance : Stacks.Ample.IsInvertibleModule X₀.toScheme L₀)
    let σ₀ : Γ(L₀, ⊤) := (pullbackGlobalSections X₀.ι L).hom σ
    have hZ₀ : Stacks.Divisors.zeroScheme X₀.toScheme L₀ σ₀ = I₀ :=
      Stacks.Divisors.zeroScheme_pullback X₀.ι L σ
    have hσ₀ : σ₀ ≠ 0 := fun h0 => ne_bot_of_isSNCFamily hsnc none <| by
      change I₀ = ⊥
      rw [← hZ₀, h0]
      exact Stacks.Divisors.zeroScheme_zero_eq_bot L₀
    have hsmT : Smooth (I₀.subschemeι ≫ sY) :=
      MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ (hsnc.1 none).2.2
    have hA : Nonempty ((Scheme.Modules.pullback I₀.subschemeι).obj
        (Scheme.Hom.relativeDifferentialForms sY (n' + 1) ⊗ L₀) ≅
          Scheme.Hom.relativeDifferentialForms (I₀.subschemeι ≫ sY) n') := by
      have : Smooth ((Stacks.Divisors.zeroScheme X₀.toScheme L₀ σ₀).subschemeι ≫ sY) := by
        rw [hZ₀]
        exact hsmT
      have := nonempty_pullback_canonical_twist_iso_zeroScheme sY (n := n') L₀ σ₀ hσ₀
      rwa [hZ₀] at this
    obtain ⟨eA⟩ := hA
    -- the open `V` as an open subscheme of the trace `V(I₀) = H ∩ X°`
    obtain ⟨k₀, hk₀, hk₀c, hk₀r⟩ :=
      MMP.Threefold.Mori.OpenRestriction.exists_openImmersion_comap_subscheme X₀.ι Z
    have hrange : Set.range (V.ι ≫ W.ι) ⊆ Set.range k₀ := by
      rintro _ ⟨v, rfl⟩
      apply hk₀r
      rw [Scheme.Opens.range_ι]
      exact v.2
    let φ : V.toScheme ⟶ I₀.subscheme := IsOpenImmersion.lift k₀ (V.ι ≫ W.ι) hrange
    have hφ : φ ≫ k₀ = V.ι ≫ W.ι := IsOpenImmersion.lift_fac _ _ _
    let κ : V.toScheme ⟶ X₀.toScheme := φ ≫ I₀.subschemeι
    have hκ : κ ≫ X₀.ι = V.ι ≫ j := by
      change (φ ≫ I₀.subschemeι) ≫ X₀.ι = V.ι ≫ W.ι ≫ Z.subschemeι
      rw [Category.assoc, hk₀c, ← Category.assoc, hφ, Category.assoc]
    -- `V` is a smooth variety
    have : Nonempty V := ⟨⟨genericPoint W, hηWX₀⟩⟩
    have : IsDominant V.ι := isDominant_opens_ι V
    let sV : V.toScheme ⟶ Spec (.of k) := V.ι ≫ W.ι ≫ Z.subschemeι ≫ X ↘ Spec (.of k)
    have hsV : sV = φ ≫ I₀.subschemeι ≫ sY := by
      change V.ι ≫ j ≫ X ↘ Spec (.of k) = (φ ≫ I₀.subschemeι) ≫ X₀.ι ≫ X ↘ Spec (.of k)
      rw [← Category.assoc, ← hκ, Category.assoc]
    have hVvar : IsNormalVariety k sV := isNormalVariety_ι hWvar V
    have : IsIntegral V.toScheme := hVvar.1.toIsIntegral
    have hsmV : Smooth sV := by
      rw [hsV]
      infer_instance
    have : IsSmoothVariety k sV := (isSmoothVariety_iff k sV).2 ⟨hVvar.1, hsmV⟩
    have : CompactSpace V.toScheme := QuasiCompact.compactSpace_of_compactSpace sV
    have hVc : ∀ D : Divisor V.toScheme, D.IsCartier :=
      (Divisor.cartier_weil_dictionary_of_isSmoothVariety k sV).1
    have hVsm : IsSmoothScheme sV := (isSmoothScheme_iff _).2 hsmV
    -- the left side: `𝒪_W(D')|_V ≅ (Ω^{n'}_V)^{⊗ m} ⊗ 𝒪_V(B'|_V)`
    obtain ⟨eL1⟩ := nonempty_divisorialSheaf_restrictOpen_iso D' V
    set K'V : Divisor V.toScheme := K'.restrictOpen V
    set B'V : Divisor V.toScheme := (B.restrictComponents j).restrictOpen V
    have hD'V : D'.restrictOpen V = (m : ℤ) • K'V + B'V := by
      ext P
      simp [K'V, B'V, hD'def, DivisorWithCoeffs.coeff_restrictOpen]
    obtain ⟨eL2⟩ := (hVc K'V).nonempty_divisorialSheaf_zsmul_add_iso (hVc B'V) m
    have hK'Vc : K'V.IsCanonicalDivisor sV n' := isCanonicalDivisor_restrictOpen hWvar hK' V
    obtain ⟨eL3⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor' hVsm hK'Vc
    obtain ⟨eL4⟩ := nonempty_tensorPow_congr eL3 m
    have eLHS : Nonempty (D'.divisorialSheaf.restrict V.ι ≅
        MMP.Intersection.Scheme.Modules.tensorPow
          (Scheme.Hom.relativeDifferentialForms sV n') m ⊗ B'V.divisorialSheaf) :=
      ⟨eL1.symm ≪≫ eqToIso (congrArg Divisor.divisorialSheaf hD'V) ≪≫ eL2 ≪≫
        whiskerRightIso eL4 _⟩
    -- the boundary on `X°` pulls back to `B'|_V`: the components of `Δ` are transverse to `H`
    set B₀ : Divisor X₀.toScheme := B.restrictOpen X₀
    have hκη : ∀ Z : irreducibleComponents V.toScheme,
        X₀.ι (κ (componentGenericPoint V.toScheme Z)) = j (genericPoint W) := by
      intro Z
      rw [← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply, componentGenericPoint_eq_genericPoint,
        map_genericPoint_of_isDominant V.ι]
    have hB₀s : ∀ Z : irreducibleComponents V.toScheme,
        κ (componentGenericPoint V.toScheme Z) ∉ B₀.supp := by
      intro Z hmem
      obtain ⟨E, hEc, hE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
      have hEB : OpenWeilRestriction.primeDivisorMap X₀.ι E ∈ B.support :=
        Finsupp.mem_support_iff.2 hEc
      have h := (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff X₀.ι E _).2 hE
      rw [hκη] at h
      exact hηWE _ (hBsupp _ hEB) h
    have hB₀l : ∀ E ∈ B₀.support, ∃ l : (Δ.restrictOpen X₀).support,
        l.1.idealSheaf = E.idealSheaf := by
      intro E hE
      have h0 : B₀ E ≠ 0 := Finsupp.mem_support_iff.1 hE
      have hEB : OpenWeilRestriction.primeDivisorMap X₀.ι E ∈ B.support :=
        Finsupp.mem_support_iff.2 h0
      have h1 : Δ (OpenWeilRestriction.primeDivisorMap X₀.ι E) ≠ 0 :=
        Finsupp.mem_support_iff.1 (hBsupp _ hEB)
      exact ⟨⟨E, Finsupp.mem_support_iff.2 h1⟩, rfl⟩
    obtain ⟨B'', hB''p, hB''c⟩ := exists_isPullback_of_support_subset sY I₀
      (fun E : (Δ.restrictOpen X₀).support => E.1.idealSheaf) hsnc φ hYc B₀ hB₀l hB₀s
    have hB''eq : B'' = B'V := by
      ext P
      change B''.coeff P =
        (B.restrictComponents j).coeff (OpenWeilRestriction.primeDivisorMap V.ι P)
      have hB' : ∀ E ∈ B.support, E.genericPoint ∉ Set.range j := fun E hE =>
        havoid E (hBsupp E hE)
      have hg : MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap V.ι P) =
          V.ι P.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap _ _
      rw [hB''c P, DivisorWithCoeffs.coeff_restrictComponents_of_pure j B hpure hB', hg]
      have hjP : j (V.ι P.genericPoint) = X₀.ι (κ P.genericPoint) := by
        rw [← Scheme.Hom.comp_apply, ← hκ, Scheme.Hom.comp_apply]
      rw [hjP]
      have hbij : Set.BijOn (OpenWeilRestriction.primeDivisorMap X₀.ι)
          (OpenWeilRestriction.primeDivisorMap X₀.ι ⁻¹' (B.support : Set _)) B.support := by
        refine ⟨fun E hE => hE, (OpenWeilRestriction.primeDivisorMap_injective X₀.ι).injOn,
          fun E' hE' => ?_⟩
        have hη : E'.genericPoint ∈ Set.range X₀.ι.base := by
          rw [Scheme.Opens.range_ι]
          exact hX₀ _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E').le
        obtain ⟨E, hE⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff X₀.ι E').2 hη
        exact ⟨E, by simpa [hE] using hE', hE⟩
      rw [← Finsupp.sum_comapDomain (OpenWeilRestriction.primeDivisorMap X₀.ι) B
        (fun E' d => if X₀.ι (κ P.genericPoint) ∈ E'.support then d else 0) hbij]
      change _ = Finsupp.sum B₀ _
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun E _ => ?_
      simp only [Function.comp,
        MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff]
      split_ifs <;> simp [DivisorWithCoeffs.coeff]
    -- `κ^* 𝒪(B₀) ≅ 𝒪_V(B'|_V)`
    obtain ⟨eB⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (hYc B₀) κ hB₀s
    have hpbB : B₀.pullback (hYc B₀) hB₀s = B'V := (hB''p.pullback_eq (hYc B₀)).trans hB''eq
    have eBV : (Scheme.Modules.pullback κ).obj B₀.divisorialSheaf ≅ B'V.divisorialSheaf :=
      eB.symm ≪≫ eqToIso (congrArg Divisor.divisorialSheaf hpbB)
    -- adjunction: `κ^*(Ω^{n'+1}_{X°} ⊗ L₀) ≅ Ω^{n'}_V`
    obtain ⟨eΩφ⟩ := nonempty_restrict_relativeDifferentialForms_iso φ (I₀.subschemeι ≫ sY)
      (φ ≫ I₀.subschemeι ≫ sY) rfl n'
    have eΩ : (Scheme.Modules.pullback κ).obj
        (Scheme.Hom.relativeDifferentialForms sY (n' + 1) ⊗ L₀) ≅
          Scheme.Hom.relativeDifferentialForms sV n' :=
      ((Scheme.Modules.pullbackComp φ I₀.subschemeι).app _).symm ≪≫
        (Scheme.Modules.pullback φ).mapIso eA ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback φ).app _).symm ≪≫ eΩφ ≪≫
        eqToIso (by rw [hsV])
    -- `𝒪_X(D)|_{X°} ≅ (Ω^{n'+1}_{X°})^{⊗ m} ⊗ 𝒪(B₀)`
    obtain ⟨eD1⟩ := nonempty_divisorialSheaf_restrictOpen_iso D X₀
    set K₀ : Divisor X₀.toScheme := K.restrictOpen X₀
    have hD₀ : D.restrictOpen X₀ = (m : ℤ) • K₀ + B₀ := by
      ext P
      simp [K₀, B₀, hBdef, DivisorWithCoeffs.coeff_restrictOpen]
    obtain ⟨eD2⟩ := (hYc K₀).nonempty_divisorialSheaf_zsmul_add_iso (hYc B₀) m
    have hYsm : IsSmoothScheme sY := (isSmoothScheme_iff _).2 hsmY
    have hK₀c : K₀.IsCanonicalDivisor sY n := isCanonicalDivisor_restrictOpen hX hK X₀
    obtain ⟨eD3⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor' hYsm hK₀c
    have eD3' : K₀.divisorialSheaf ≅ Scheme.Hom.relativeDifferentialForms sY (n' + 1) :=
      eD3 ≪≫ eqToIso (by rw [hnn]; push_cast; rfl)
    obtain ⟨eD4⟩ := nonempty_tensorPow_congr eD3' m
    obtain ⟨eLm⟩ := nonempty_pullback_tensorPow_iso X₀.ι L m
    obtain ⟨eT⟩ := nonempty_tensorPow_tensor_iso
      (Scheme.Hom.relativeDifferentialForms sY (n' + 1)) L₀ m
    obtain ⟨eTκ⟩ := nonempty_pullback_tensorPow_iso κ
      (Scheme.Hom.relativeDifferentialForms sY (n' + 1) ⊗ L₀) m
    obtain ⟨eΩm⟩ := nonempty_tensorPow_congr eΩ m
    obtain ⟨eL⟩ := eLHS
    refine ⟨eL ≪≫ (?_ : ((Scheme.Modules.pullback j).obj
      (D.divisorialSheaf ⊗ MMP.Intersection.Scheme.Modules.tensorPow L m)).restrict V.ι ≅ _).symm⟩
    exact (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _ ≪≫
      (Scheme.Modules.pullbackComp V.ι j).app _ ≪≫
      (Scheme.Modules.pullbackCongr hκ.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp κ X₀.ι).app _).symm ≪≫
      (Scheme.Modules.pullback κ).mapIso
        (Stacks.RelativeVeryAmple.pullbackTensorModulesIso X₀.ι _ _ ≪≫
          tensorIso (((Scheme.Modules.restrictFunctorIsoPullback X₀.ι).app _).symm ≪≫ eD1.symm ≪≫
            eqToIso (congrArg Divisor.divisorialSheaf hD₀) ≪≫ eD2 ≪≫ whiskerRightIso eD4 _) eLm ≪≫
          α_ _ _ _ ≪≫ whiskerLeftIso _ (braidModules _ _) ≪≫ (α_ _ _ _).symm ≪≫
          whiskerRightIso eT.symm _) ≪≫
      Stacks.RelativeVeryAmple.pullbackTensorModulesIso κ _ _ ≪≫ tensorIso (eTκ ≪≫ eΩm) eBV
  have hlin := MMP.Threefold.Mori.CanonUniq.linearlyEquivalent_of_iso hV
    (eV ≪≫ (Scheme.Modules.restrictFunctor V.ι).mapIso eE₀.symm)
  exact ⟨D', hD'eq, Divisor.IsCartier.of_linearlyEquivalent hlin hE₀c,
    ⟨hlin.divisorialSheafIso ≪≫ eE₀⟩⟩

/-- The conclusion for one connected component `W` of a member `Z(σ)` satisfying the genericity
conditions produced by the Bertini theorems. -/
private theorem member_step [IsAlgClosed k] [CharZero k] [IsLocallyNoetherian X] [IsNormal X]
    {Δ : QDivisor X} (hΔ : IsPair (X ↘ Spec (.of k)) Δ)
    (X₀ : X.Opens) (hX₀sm : X₀ ≤ smoothLocus (X ↘ Spec (.of k)))
    (hX₀ : ∀ x : X, Order.coheight x ≤ 1 → x ∈ X₀)
    (σ : Γ(L, ⊤))
    (hnormal : IsNormal (Stacks.Divisors.zeroScheme X L σ).subscheme)
    (hgen : ∃ x, x ∈ nonvanishingOpen X L σ)
    (havoidΔ : ∀ E ∈ Δ.support, ((E.support : Set X) ∩ nonvanishingOpen X L σ).Nonempty)
    (havoidC : ∀ Y ∈ MMP.Resolution.componentsOf ((X₀ : Set X)ᶜ),
      (Y ∩ nonvanishingOpen X L σ).Nonempty)
    (hsnc : MMP.Resolution.IsSNCFamily (X₀.ι ≫ X ↘ Spec (.of k))
      (fun o : Option (Δ.restrictOpen X₀).support =>
        o.elim ((Stacks.Divisors.zeroScheme X L σ).comap X₀.ι) fun E => E.1.idealSheaf)) :
    haveI : IsLocallyNoetherian (Stacks.Divisors.zeroScheme X L σ).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (Stacks.Divisors.zeroScheme X L σ).subschemeι
    ∀ W : (Stacks.Divisors.zeroScheme X L σ).subscheme.Opens,
      IsClopen (W : Set (Stacks.Divisors.zeroScheme X L σ).subscheme) →
      _root_.IsConnected (W : Set (Stacks.Divisors.zeroScheme X L σ).subscheme) →
      ∃ hW : IsNormalVariety k
          (W.ι ≫ (Stacks.Divisors.zeroScheme X L σ).subschemeι ≫ X ↘ Spec (.of k)),
        (∀ E ∈ Δ.support, E.genericPoint ∉ Set.range
          (W.ι ≫ (Stacks.Divisors.zeroScheme X L σ).subschemeι)) ∧
        ∀ (m : ℕ), 0 < m → ∀ (n n' : ℕ) (K : Divisor X) (K' : Divisor W.toScheme),
          K.IsCanonicalDivisor (X ↘ Spec (.of k)) n →
          (haveI := hW.2;
            K'.IsCanonicalDivisor (W.ι ≫
              (Stacks.Divisors.zeroScheme X L σ).subschemeι ≫ X ↘ Spec (.of k)) n') →
          ∀ D : Divisor X, Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor K + Δ) →
            D.IsCartier →
            haveI := hW.2
            ∃ D' : Divisor W.toScheme,
              Divisor.toQDivisor D' = (m : ℤ) • (Divisor.toQDivisor K' +
                Δ.restrictComponents
                  (W.ι ≫ (Stacks.Divisors.zeroScheme X L σ).subschemeι)) ∧
              D'.IsCartier ∧
              Nonempty (D'.divisorialSheaf ≅ (Scheme.Modules.pullback
                (W.ι ≫ (Stacks.Divisors.zeroScheme X L σ).subschemeι)).obj
                  (D.divisorialSheaf ⊗
                    MMP.Intersection.Scheme.Modules.tensorPow L m)) := by
  intro W hWc hWconn
  classical
  have hX := hΔ.1
  have : AlgebraicGeometry.IsVariety k (X ↘ Spec (.of k)) := hX.1
  have : IsIntegral X := hX.1.toIsIntegral
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  let Z := Stacks.Divisors.zeroScheme X L σ
  have : IsLocallyNoetherian Z.subscheme := LocallyOfFiniteType.isLocallyNoetherian Z.subschemeι
  let j : W.toScheme ⟶ X := W.ι ≫ Z.subschemeι
  have hσ : σ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hgen
    rw [Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff, map_zero] at hx
    exact hx (Submodule.zero_mem _)
  have hZeff : Stacks.Divisors.IsEffectiveCartierDivisor Z :=
    isEffectiveCartierDivisor_zeroScheme_of_ne_zero L σ hσ
  -- `W` is a normal variety
  have : CompactSpace Z.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace Z.subschemeι
  have : IsNoetherian Z.subscheme := ⟨⟩
  have : CompactSpace W := isCompact_iff_compactSpace.mp hWc.isClosed.isCompact
  have : IsNoetherian W := ⟨⟩
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hWconn
  have : IsNormal Z.subscheme := hnormal
  have : IrreducibleSpace W := irreducibleSpace_of_isNormal_of_connectedSpace
  have : IsIntegral W := isIntegral_of_irreducibleSpace_of_isReduced W
  have hWvar : IsNormalVariety k (j ≫ X ↘ Spec (.of k)) := by
    refine ⟨?_, inferInstance⟩
    refine (MMP.Mori.isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [quasiCompact_iff_forall_isAffineOpen]
    exact fun U _ => NoetherianSpace.isCompact _
  -- the coheight of a point of `W` in `X` is one more than its coheight in `W`
  have hcoh : ∀ w : W.toScheme, Order.coheight (j w) = Order.coheight w + 1 := fun w => by
    change Order.coheight (Z.subschemeι (W.ι w)) = _
    rw [coheight_subschemeι_eq_add_one Z hZeff]
    congr 1
    exact coheight_eq_of_isOpenImmersion (x := w) W.ι
  -- `W` contains no component of `Δ`
  have havoid : ∀ E ∈ Δ.support, E.genericPoint ∉ Set.range j := by
    rintro E hE ⟨w, hw⟩
    obtain ⟨x, hxE, hxnv⟩ := havoidΔ E hE
    have hηZ : E.genericPoint ∈ (Z.support : Set X) := by
      rw [← Z.range_subschemeι, ← hw]
      exact ⟨W.ι w, rfl⟩
    have hxZ : x ∈ (Z.support : Set X) := by
      have hEsub : (E.support : Set X) ⊆ Z.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact closure_minimal (Set.singleton_subset_iff.2 hηZ) Z.support.isClosed
      exact hEsub hxE
    exact notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen L σ hxnv
      (Z.mem_supportSet_iff_mem_support.2 hxZ)
  refine ⟨hWvar, havoid, ?_⟩
  intro m _ n n' K K' hK hK' D hD hDc
  exact adjunction_step hΔ X₀ hX₀sm hX₀ σ havoidC hsnc W hWc.isClosed hWvar hcoh havoid
    m n n' K K' hK hK' D hD hDc

/-- **Adjunction for a general member of a free linear system.** Let `k` be algebraically closed
of characteristic zero, `(X, Δ)` a pair over `k` with `dim X ≥ 2`, and `s₀, …, s_N` sections of
an invertible sheaf `L` spanning a free linear system. There is a dense open `U ⊆ ℙ(V)` such that
for every `c ≠ 0` with `[c] ∈ U` and every connected component `H⁰` of `H = Z(∑ᵢ cᵢ sᵢ)`, with
inclusion `ι : H⁰ ⟶ X`:
* `H⁰` is a normal variety over `k`;
* no component of `Δ` is contained in `H⁰`;
* for every `m > 0`, every canonical divisor `K_X` of `X` and `K_{H⁰}` of `H⁰`, and every
  Cartier divisor `D` with `D = m(K_X + Δ)`, there is a Cartier divisor `D'` on `H⁰` with
  `D' = m(K_{H⁰} + Δ|_{H⁰})` and `𝒪_{H⁰}(D') ≅ ι^*(𝒪_X(D) ⊗ L^{⊗ m})`. -/
@[mmp "lem_km5d_general_member_pair"]
public theorem IsPair.exists_dense_open_adjunction_connectedComponent_zeroScheme
    [IsAlgClosed k] [CharZero k] [IsLocallyNoetherian X] [IsNormal X] {Δ : QDivisor X}
    (hΔ : IsPair (X ↘ Spec (.of k)) Δ) (hdim : 2 ≤ topologicalKrullDim X)
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤) :
    ∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        haveI : IsLocallyNoetherian
            (Stacks.Divisors.zeroScheme X L (systemSection s c)).subscheme :=
          LocallyOfFiniteType.isLocallyNoetherian
            (Stacks.Divisors.zeroScheme X L (systemSection s c)).subschemeι
        ∀ W : (Stacks.Divisors.zeroScheme X L (systemSection s c)).subscheme.Opens,
          IsClopen (W : Set (Stacks.Divisors.zeroScheme X L (systemSection s c)).subscheme) →
          _root_.IsConnected
            (W : Set (Stacks.Divisors.zeroScheme X L (systemSection s c)).subscheme) →
          ∃ hW : IsNormalVariety k
              (W.ι ≫ (Stacks.Divisors.zeroScheme X L (systemSection s c)).subschemeι ≫
                X ↘ Spec (.of k)),
            (∀ E ∈ Δ.support, E.genericPoint ∉ Set.range
              (W.ι ≫ (Stacks.Divisors.zeroScheme X L (systemSection s c)).subschemeι)) ∧
            ∀ (m : ℕ), 0 < m → ∀ (n n' : ℕ) (K : Divisor X) (K' : Divisor W.toScheme),
              K.IsCanonicalDivisor (X ↘ Spec (.of k)) n →
              (haveI := hW.2;
                K'.IsCanonicalDivisor (W.ι ≫
                  (Stacks.Divisors.zeroScheme X L (systemSection s c)).subschemeι ≫
                    X ↘ Spec (.of k)) n') →
              ∀ D : Divisor X, Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor K + Δ) →
                D.IsCartier →
                haveI := hW.2
                ∃ D' : Divisor W.toScheme,
                  Divisor.toQDivisor D' = (m : ℤ) • (Divisor.toQDivisor K' +
                    Δ.restrictComponents
                      (W.ι ≫ (Stacks.Divisors.zeroScheme X L (systemSection s c)).subschemeι)) ∧
                  D'.IsCartier ∧
                  Nonempty (D'.divisorialSheaf ≅ (Scheme.Modules.pullback
                    (W.ι ≫ (Stacks.Divisors.zeroScheme X L (systemSection s c)).subschemeι)).obj
                      (D.divisorialSheaf ⊗
                        MMP.Intersection.Scheme.Modules.tensorPow L m)) := by
  classical
  have hX := hΔ.1
  have : AlgebraicGeometry.IsVariety k (X ↘ Spec (.of k)) := hX.1
  have : PerfectField k := PerfectField.ofCharZero
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  obtain ⟨X₀, hX₀sm, hX₀snc, hX₀⟩ :=
    exists_isSNC_restrictOpen_of_isNormalVariety (X ↘ Spec (.of k)) hX Δ
  -- normality of the general member
  obtain ⟨U₁, hU₁, hN⟩ :=
    exists_dense_open_isNormal_zeroScheme_of_two_le_topologicalKrullDim hdim s hs
  -- the general member contains no component of `Δ` and no component of `X ∖ X°`
  have hCfin := (MMP.Resolution.Aux.finite_and_cover_componentsOf
    (X₀.isOpen.isClosed_compl)).1
  have : Finite (MMP.Resolution.componentsOf ((X₀ : Set X)ᶜ)) := hCfin.to_subtype
  let Zf : Option (Δ.support ⊕ MMP.Resolution.componentsOf ((X₀ : Set X)ᶜ)) → Set X :=
    fun o => o.elim Set.univ (Sum.elim (fun E => (E.1.support : Set X)) (fun Y => Y.1))
  have hZc : ∀ o, IsClosed (Zf o) := by
    rintro (_ | (E | Y))
    · exact isClosed_univ
    · exact E.1.idealSheaf.support.isClosed
    · exact MMP.Resolution.Aux.isClosed_of_mem_componentsOf X₀.isOpen.isClosed_compl Y.2
  have hZi : ∀ o, IsIrreducible (Zf o) := by
    rintro (_ | (E | Y))
    · exact IrreducibleSpace.isIrreducible_univ X
    · change IsIrreducible (E.1.support : Set X)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    · exact Y.2.1.1
  obtain ⟨-, U₂, hU₂, hA⟩ := exists_dense_open_inter_nonvanishingOpen_nonempty hX.1 s hs Zf hZc hZi
  -- the general member is transverse to `Δ` on `X°`
  have hsm₀ : Smooth (X₀.ι ≫ X ↘ Spec (.of k)) := smooth_ι_comp_of_le_smoothLocus X₀ hX₀sm
  obtain ⟨-, U₃, hU₃, hS⟩ := exists_dense_open_isSNCFamily_zeroScheme s hs X₀.ι
    (fun E : (Δ.restrictOpen X₀).support => E.1.idealSheaf) hX₀snc.isSNCFamily_idealSheaf
  refine ⟨U₁ ⊓ U₂ ⊓ U₃, ?_, fun c hc hcU => ?_⟩
  · rw [Opens.coe_inf, Opens.coe_inf]
    exact ((hU₁.inter_of_isOpen_left hU₂ U₁.isOpen).inter_of_isOpen_left hU₃
      (U₁.isOpen.inter U₂.isOpen))
  obtain ⟨-, -, hsncc⟩ := hS c hc hcU.2
  have hAc := hA c hc hcU.1.2
  exact member_step hΔ X₀ hX₀sm hX₀ (systemSection s c) (hN c hc hcU.1.1)
    ⟨_, (hAc none).some_mem.2⟩
    (fun E hE => hAc (some (Sum.inl ⟨E, hE⟩)))
    (fun Y hY => hAc (some (Sum.inr ⟨Y, hY⟩))) hsncc

end Member

end MMP.Mori

end
