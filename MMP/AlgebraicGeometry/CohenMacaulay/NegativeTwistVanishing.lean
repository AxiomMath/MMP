module
public import MMP.AlgebraicGeometry.Positivity.AmpleTwistRealPerturbation
public import MMP.AlgebraicGeometry.Cohomology.SheafHModules
public import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesBertiniCutStep
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalSectionsDerived
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryStepCokernelDim
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceComponentModule
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingSectionsCotangent
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictScalarsDerived
public import StacksFrontier.AlgebraicGeometry.Properties.DimensionFunctionClosure
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight

/-!
# Vanishing of negative twists implies Cohen–Macaulay

Let `X` be a projective scheme over a field `k`, `L` an ample invertible sheaf on `X` and `F` a
coherent sheaf on `X` whose support is pure of dimension `n`. If `H^i(X, F ⊗ L^{-r}) = 0` for all
`i < n` and all sufficiently large `r`, then `F` is Cohen–Macaulay: every stalk `F_x` is a
Cohen–Macaulay `𝒪_{X,x}`-module. The proof is by induction on `n`, cutting the support by the
zero scheme of a section of a positive power of `L` that avoids the associated points of `F`.

## Main results

* `MMP.Mori.isCMSheaf_of_eventually_subsingleton_sheafCohomology_tensorPowModule_neg`

## Implementation notes

The support of `F` is the set of points where the stalk of `F` is nontrivial, and "pure of
dimension `n`" means that every irreducible component of the support (as a subspace) has
topological Krull dimension `n`. The twist `F ⊗ L^{-r}` uses the integer tensor powers
`Stacks.Ample.tensorPowModule` of the invertible sheaf `L`, and `H^i` is
Mathlib's sheaf cohomology `CategoryTheory.Sheaf.H` of the underlying sheaf of abelian groups.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998], Cor. 5.72.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.ModuleStalkSpecialization
open scoped Pointwise

universe u

namespace MMP.Mori

/-- The hypotheses of the statement, for fixed `k` and `n`, as a predicate on `(X, L, F)`. -/
private def Hyp (k : Type u) [Field k] (n : ℕ) (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (F : X.Modules) : Prop :=
  IsProjectiveMorphism (X ↘ Spec (.of k)) ∧ MMP.Intersection.IsAmple k L ∧
    SheafOfModules.IsCoherent F ∧
    (∀ Z ∈ irreducibleComponents
        {x : X | Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)},
      topologicalKrullDim Z = n) ∧
    (∀ᶠ r : ℕ in Filter.atTop, ∀ i < n,
      Subsingleton (Sheaf.H.{u}
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (F ⊗ (Stacks.Ample.tensorPowModule X L (-(r : ℤ)) : X.Modules) : X.Modules)) i))

/-- On a projective `k`-scheme, a coherent sheaf whose stalks at closed points are
Cohen–Macaulay is Cohen–Macaulay. -/
private theorem isCMSheaf_of_forall_isClosed (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (hX : IsProjectiveMorphism (X ↘ Spec (.of k)))
    (F : X.Modules) [SheafOfModules.IsCoherent F]
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      IsCMModule (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    IsCMSheaf F := by
  intro y
  have : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism _ hX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  obtain ⟨x, hx, hc⟩ := isClosed_closure.exists_closed_singleton (Set.singleton_nonempty y).closure
  have hs : y ⤳ x := specializes_iff_mem_closure.mpr hx
  have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType (M := F)
  letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes hs).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk y)
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)) :=
    Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hs
  letI := stalkModule F x
  letI := stalkModule F y
  letI := stalkSpecializesModule F hs
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    SheafOfModules.finite_stalk X.sheaf F x
  have hcm : IsCMModule (X.presheaf.stalk x) (F.presheaf.stalk x) := h x hc
  have := isLocalizedModule_atPrime_stalkSpecializes F hs
  have : IsScalarTower (X.presheaf.stalk x) (X.presheaf.stalk y) (F.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  change IsCMModule (X.presheaf.stalk y) (F.presheaf.stalk y)
  exact hcm.of_isLocalizedModule
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x))
    (X.presheaf.stalk y) (stalkSpecializesₗ F hs)

/-- In a `T0` space, if every irreducible component of a subset `S` has dimension `0`, then
specialization between points of `S` is trivial. -/
private theorem eq_of_specializes_of_forall_topologicalKrullDim_eq_zero {X : Type*}
    [TopologicalSpace X] [T0Space X] {S : Set X}
    (hS : ∀ Z ∈ irreducibleComponents S, topologicalKrullDim Z = 0) {a b : S} (h : a ⤳ b) :
    a = b := by
  obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := a)).closure
  have ha : a ∈ Z := hsub (subset_closure rfl)
  have hb : b ∈ Z := hsub (specializes_iff_mem_closure.mp h)
  by_contra hne
  have h' : (⟨a, ha⟩ : Z) ⤳ ⟨b, hb⟩ := (subtype_specializes_iff _ _).mpr h
  have hlt : (⟨closure {(⟨b, hb⟩ : Z)}, isIrreducible_singleton.closure, isClosed_closure⟩ :
      TopologicalSpace.IrreducibleCloseds Z) <
      ⟨closure {(⟨a, ha⟩ : Z)}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    refine lt_of_le_of_ne h'.closure_subset fun he => hne ?_
    have := congrArg TopologicalSpace.IrreducibleCloseds.carrier he
    exact congrArg Subtype.val
      ((specializes_iff_closure_subset.mpr this.ge).antisymm h').symm.eq
  have h0 := hS Z hZ
  rw [topologicalKrullDim] at h0
  have : (0 : WithBot ℕ∞) < Order.krullDim (TopologicalSpace.IrreducibleCloseds Z) :=
    Order.krullDim_pos_iff.mpr ⟨_, _, hlt⟩
  simp_all

/-- If the support of `F` is pure of dimension `0`, every stalk `F_x` is Cohen–Macaulay. -/
private theorem isCMModule_stalk_of_zero (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (F : X.Modules) (hF : Hyp k 0 X L F) (x : X) :
    IsCMModule (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) := by
  obtain ⟨-, -, hcoh, hdim, -⟩ := hF
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  rcases subsingleton_or_nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) with
    hx | hx
  · exact Or.inl hx
  refine Or.inr ⟨[], ⟨by simp, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩, ?_⟩
  have hS : ∀ Z ∈ irreducibleComponents
      {x : X | Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)},
      topologicalKrullDim Z = 0 := fun Z hZ => (hdim Z hZ).trans (by simp)
  have hsupp : ∀ p ∈ Module.support (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x),
      p = IsLocalRing.closedPoint (X.presheaf.stalk x) := by
    intro p hp
    obtain ⟨y, h, hyp⟩ := MMP.Foundations.exists_specializes_stalkSpecializationPrime_eq x p.asIdeal
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    letI := stalkModule F x
    letI := stalkModule F y
    letI := stalkSpecializesModule F h
    have hlm := isLocalizedModule_atPrime_stalkSpecializes F h
    have hP : (IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x) =
        p.asIdeal := hyp
    have hnt : Nontrivial (LocalizedModule
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)).primeCompl
        (F.presheaf.stalk x)) := by
      have hc : ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under
          (X.presheaf.stalk x)).primeCompl = p.asIdeal.primeCompl := by
        ext; simp [Ideal.primeCompl, hP]
      rw [hc]; exact Module.mem_support_iff.mp hp
    have hy : Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      (IsLocalizedModule.iso
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)).primeCompl
        (stalkSpecializesₗ F h)).symm.toEquiv.nontrivial
    have hxy := eq_of_specializes_of_forall_topologicalKrullDim_eq_zero hS
      (a := ⟨y, hy⟩) (b := ⟨x, hx⟩) ((subtype_specializes_iff _ _).mpr h)
    cases congrArg Subtype.val hxy
    ext1
    rw [← hyp, MMP.Foundations.stalkSpecializationPrime, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have : Nonempty (Module.support (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :=
    (Module.nonempty_support_of_nontrivial).to_subtype
  have : Subsingleton (Module.support (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :=
    ⟨fun p q => Subtype.ext ((hsupp p p.2).trans (hsupp q q.2).symm)⟩
  unfold Module.supportDim
  rw [Order.krullDim_eq_zero]
  rfl

/-- Cohen–Macaulayness of a module over a local ring is invariant under linear equivalence. -/
private theorem isCMModule_of_linearEquiv {R : Type*} [CommRing R] [IsLocalRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (h : IsCMModule R M) : IsCMModule R N := by
  rcases h with h | ⟨xs, ⟨hm, hreg⟩, hlen⟩
  · exact Or.inl e.symm.toEquiv.subsingleton
  · refine Or.inr ⟨xs, ⟨hm, (e.isWeaklyRegular_congr xs).mp hreg⟩, ?_⟩
    rw [hlen, Module.supportDim, Module.supportDim, e.support_eq]

/-- In a Noetherian quasi-sober space, if no point `y ≠ x` of an open `W ∋ x` with `P y`
specializes to the closed point `x`, and `{y ∈ W | ¬ P y}` is open, then `x` has an open
neighbourhood `W' ⊆ W` in which `x` is the only point satisfying `P`. -/
private theorem exists_open_forall_eq_of_specializes {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {x : X} (hx : IsClosed ({x} : Set X))
    {W : Set X} (hW : IsOpen W) (hxW : x ∈ W) (P : X → Prop)
    (hP : IsOpen {y | y ∈ W ∧ ¬ P y}) (hspec : ∀ y ∈ W, P y → y ⤳ x → y = x) :
    ∃ W' : Set X, IsOpen W' ∧ x ∈ W' ∧ W' ⊆ W ∧ ∀ y ∈ W', P y → y = x := by
  set A : Set X := {y | y ∈ W ∧ P y ∧ y ≠ x}
  obtain ⟨S, hSf, hScl, hSirr, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure (s := A))
  set T : Set (Set X) := {t ∈ S | ¬ t ⊆ {x}}
  have hTf : T.Finite := hSf.subset (fun t ht => ht.1)
  have hKcl : IsClosed (⋃₀ T) := hTf.isClosed_sUnion (fun t ht => hScl t ht.1)
  have hAK : A ⊆ ⋃₀ T := by
    intro y hy
    have : y ∈ ⋃₀ S := hS ▸ subset_closure hy
    obtain ⟨t, htS, hyt⟩ := this
    exact ⟨t, ⟨htS, fun h => hy.2.2 (h hyt)⟩, hyt⟩
  have hxK : x ∉ ⋃₀ T := by
    rintro ⟨t, ⟨htS, htx⟩, hxt⟩
    have hgen := (hSirr t htS).isGenericPoint_genericPoint_closure
    rw [(hScl t htS).closure_eq] at hgen
    set η := (hSirr t htS).genericPoint
    have hηx : η ⤳ x := hgen.specializes hxt
    have hηW : η ∈ W := hηx.mem_open hW hxW
    have hηC : η ∈ closure A := hS ▸ ⟨t, htS, hgen.mem⟩
    have hPη : P η := by
      by_contra hn
      obtain ⟨z, ⟨_, hz⟩, hzA⟩ := mem_closure_iff.mp hηC _ hP ⟨hηW, hn⟩
      exact hz hzA.2.1
    have hη : η = x := hspec η hηW hPη hηx
    apply htx
    rw [← hgen.def, hη, hx.closure_eq]
  refine ⟨W ∩ (⋃₀ T)ᶜ, hW.inter hKcl.isOpen_compl, ⟨hxW, hxK⟩, Set.inter_subset_left, ?_⟩
  rintro y ⟨hyW, hyK⟩ hPy
  by_contra hne
  exact hyK (hAK ⟨hyW, hPy, hne⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem eq_of_isLocalHom_stalkSpecializes {X : Scheme.{u}} {x y : X} (h : y ⤳ x)
    [IsLocalHom (X.presheaf.stalkSpecializes h).hom] : y = x := by
  have : (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk x)
      (IsLocalRing.closedPoint (X.presheaf.stalk y)) = x := by
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk h, Scheme.fromSpecStalk_closedPoint] at this
  exact this

/-- An element of `F_x` killed by `𝔪_x` specializes to zero at every proper generization. -/
private theorem stalkSpecializes_eq_zero_of_forall_smul_eq_zero {X : Scheme.{u}}
    (F : X.Modules) {x y : X} (h : y ⤳ x) (hne : y ≠ x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x), a • m = 0) :
    F.presheaf.stalkSpecializes h m = 0 := by
  have hnl : ¬ IsLocalHom (X.presheaf.stalkSpecializes h).hom := fun hl =>
    hne (eq_of_isLocalHom_stalkSpecializes h)
  obtain ⟨a, hua, hna⟩ : ∃ a, IsUnit ((X.presheaf.stalkSpecializes h).hom a) ∧ ¬ IsUnit a := by
    by_contra hc
    push Not at hc
    exact hnl ⟨hc⟩
  letI := stalkModule F x
  letI := stalkModule F y
  have h0 := stalkSpecializes_smul F h a m
  erw [hm a ((IsLocalRing.mem_maximalIdeal _).mpr hna), map_zero] at h0
  exact (hua.smul_eq_zero).mp h0.symm

/-- A section `t` over `W` whose germs vanish at every point of an open `V ≤ W` other than a
closed point `x ∈ V` extends `t|_V` to a global section. -/
theorem exists_res_eq_of_germ_eq_zero {X : Scheme.{u}} (F : X.Modules) {x : X}
    (hx : IsClosed ({x} : Set X)) {V W : X.Opens} (hVW : V ≤ W) (hxV : x ∈ V) (t : Γ(F, W))
    (hzero : ∀ y, y ∈ V → y ≠ x → ∀ hy : y ∈ W, F.presheaf.germ W y hy t = 0) :
    ∃ σ : Γ(F, ⊤), F.presheaf.map (homOfLE le_top).op σ = F.presheaf.map (homOfLE hVW).op t := by
  let 𝓕 : TopCat.Sheaf Ab.{u} X := (SheafOfModules.toSheaf X.ringCatSheaf).obj F
  let U : Bool → X.Opens := fun b => cond b V ⟨{x}ᶜ, hx.isOpen_compl⟩
  let sf : ∀ b : Bool, ToType (𝓕.1.obj (Opposite.op (U b))) := fun b =>
    Bool.casesOn (motive := fun b => ToType (𝓕.1.obj (Opposite.op (U b)))) b 0
      (F.presheaf.map (homOfLE hVW).op t)
  have hres0 : 𝓕.1.map (TopologicalSpace.Opens.infLELeft V (U false)).op
      (F.presheaf.map (homOfLE hVW).op t) = 0 := by
    refine TopCat.Presheaf.section_ext 𝓕 _ _ _ fun y hy => ?_
    rw [map_zero]
    change F.presheaf.germ _ y hy (F.presheaf.map _ (F.presheaf.map _ t)) = 0
    rw [F.presheaf.germ_res_apply, F.presheaf.germ_res_apply]
    exact hzero y hy.1 hy.2 _
  have hcompat : TopCat.Presheaf.IsCompatible 𝓕.1 U sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · change 𝓕.1.map _ 0 = 𝓕.1.map (TopologicalSpace.Opens.infLERight (U false) V).op
        (F.presheaf.map (homOfLE hVW).op t)
      rw [map_zero]
      refine (TopCat.Presheaf.section_ext 𝓕 _ _ _ fun y hy => ?_).symm
      rw [map_zero]
      change F.presheaf.germ _ y hy (F.presheaf.map _ (F.presheaf.map _ t)) = 0
      rw [F.presheaf.germ_res_apply, F.presheaf.germ_res_apply]
      exact hzero y hy.2 hy.1 _
    · change 𝓕.1.map _ (F.presheaf.map (homOfLE hVW).op t) = 𝓕.1.map _ 0
      rw [map_zero]
      exact hres0
    · rfl
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro y _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hy : y = x
    · exact ⟨true, hy ▸ hxV⟩
    · exact ⟨false, hy⟩
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' 𝓕 U ⊤ (fun _ => homOfLE le_top)
    hcover sf hcompat
  exact ⟨σ, hσ true⟩

/-- On a Noetherian scheme, if the stalk `F_x` at a closed point `x` has a nonzero element killed
by `𝔪_x`, then some global section of `F` has nonzero germ at `x`. -/
private theorem exists_section_germ_ne_zero_of_forall_smul_eq_zero {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (F : X.Modules) {x : X} (hx : IsClosed ({x} : Set X))
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) (hm0 : m ≠ 0)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x), a • m = 0) :
    ∃ σ : Γ(F, ⊤), F.presheaf.germ ⊤ x trivial σ ≠ 0 := by
  obtain ⟨W, hxW, t, ht⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
  set P : X → Prop := fun y => ¬ ∀ hy : y ∈ W, F.presheaf.germ W y hy t = 0 with hPdef
  have hP : IsOpen {y | y ∈ W ∧ ¬ P y} := by
    simpa only [hPdef, not_not] using isOpen_germ_eq_zero F W t
  have hspec : ∀ y ∈ W, P y → y ⤳ x → y = x := by
    intro y hyW hPy hyx
    by_contra hne
    refine hPy fun hy => ?_
    rw [← germ_stalkSpecializes_apply F hxW hyx t, ht]
    exact stalkSpecializes_eq_zero_of_forall_smul_eq_zero F hyx hne m hm
  obtain ⟨W', hW'o, hxW', hW'W, hW'⟩ :=
    exists_open_forall_eq_of_specializes hx W.isOpen hxW P hP hspec
  let V : X.Opens := ⟨W', hW'o⟩
  have hVW : V ≤ W := hW'W
  obtain ⟨σ, hσ⟩ := exists_res_eq_of_germ_eq_zero F hx hVW hxW' t fun y hyV hne => by
    by_contra hc
    exact hne (hW' y hyV hc)
  refine ⟨σ, fun h0 => hm0 ?_⟩
  have h2 := congrArg (F.presheaf.germ V x hxW') hσ
  rw [F.presheaf.germ_res_apply, F.presheaf.germ_res_apply, ht] at h2
  rwa [← h2]

/-! ### Sections avoiding associated points

Choosing a section of `L^{⊗r}` that vanishes at a closed point `x` and at no associated point of
`F` (`eventually_exists_section_notMem_nonvanishingLocus`), and injectivity of multiplication by
it (`mono_mul_of_forall_isAssociatedPoint_mem_nonvanishingLocus`). -/

section SectionAvoidingAssociatedPoints

open MMP.Intersection.Scheme.Modules (tensorPow)

private theorem isNoetherian_of_isProjectiveMorphism (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (hX : IsProjectiveMorphism (X ↘ Spec (.of k))) : IsNoetherian X := by
  have : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism _ hX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  exact AlgebraicGeometry.IsNoetherian.mk

/-- Tensor powers of an invertible module are invertible. -/
private theorem isInvertibleModule_tensorPow {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (r : ℕ) :
    Stacks.Ample.IsInvertibleModule X (tensorPow L r) := by
  induction r with
  | zero => exact Stacks.Ample.isInvertibleModule_unit X
  | succ n ih =>
    have h1 : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorPow L n) :=
      ih
    have h2 : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := ‹_›
    exact Stacks.Chow.isInvertible_tensorObj (tensorPow L n) L

/-- Left whiskering for the monoidal structure on `X.Modules` is
`AlgebraicGeometry.Scheme.Modules.tensorLeftMap`. -/
private theorem whiskerLeft_eq_tensorLeftMap {X : Scheme.{u}} (F G H : X.Modules) (φ : G ⟶ H) :
    F ◁ φ = (Scheme.Modules.tensorLeftMap F φ : F ⊗ G ⟶ F ⊗ H) := by
  rw [← id_tensorHom]
  have := Stacks.SheafOfModules.OnSpace.monoidal_tensorHom X.toRingedSpace (𝟙 F) φ
  erw [Category.id_comp, Category.comp_id] at this
  refine this.trans ?_
  erw [Functor.uncurry_obj_map]
  exact (congrArg (· ≫ _) (congrArg (fun t => NatTrans.app t G)
    (CategoryTheory.Functor.map_id _ F))).trans (Category.id_comp _)

/-- If `u : F ⟶ F ⊗ A` and `g : A ⟶ B` are bijective on stalks at `ξ`, then `u ≫ F ◁ g` is
injective on stalks at `ξ`. -/
private theorem injective_stalkLinearMap_comp_whiskerLeft {X : Scheme.{u}} (F A B : X.Modules)
    (u : F ⟶ F ⊗ A) (g : A ⟶ B) (ξ : X)
    (hu : Function.Bijective (stalkLinearMap _ _ u ξ))
    (hg : Function.Bijective (stalkLinearMap A B g ξ)) :
    Function.Injective (stalkLinearMap F (F ⊗ B) (u ≫ F ◁ g) ξ) := by
  rw [whiskerLeft_eq_tensorLeftMap]
  exact (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_comp _ _ ξ hu
    (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_tensorLeftMap F g ξ hg)).injective

/-- Multiplication by a section `s` of a line bundle `M` is injective on a coherent sheaf `F` as
soon as `s` vanishes at no associated point of `F`. -/
private theorem mono_mul_of_forall_isAssociatedPoint_mem_nonvanishingLocus (k : Type u)
    [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsNoetherian X] (F : X.Modules)
    [SheafOfModules.IsCoherent F] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (r : ℕ)
    (s : MMP.Intersection.H0 k (tensorPow L r))
    (h : ∀ ξ, Stacks.Divisors.IsAssociatedPoint F ξ →
      ξ ∈ Stacks.Ample.nonvanishingLocus (tensorPow L r) s) :
    Mono ((ρ_ F).inv ≫ F ◁ (SheafOfModules.unitHomEquiv (tensorPow L r)).symm
      s.toSections) := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : Stacks.Ample.IsInvertibleModule X (tensorPow L r) := isInvertibleModule_tensorPow L r
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent (M := F)
  have : (tensorPow L r).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have : (F ⊗ tensorPow L r).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace F _ ‹_› ‹_›
  have hφ : (SheafOfModules.unitHomEquiv (tensorPow L r)).symm s.toSections =
      Stacks.EnriquesSeveriZariski.sectionHom (tensorPow L r) s := rfl
  refine Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints
    _ fun ξ => ?_
  by_cases hξ : Stacks.Divisors.IsAssociatedPoint F ξ
  · left
    rw [hφ]
    exact injective_stalkLinearMap_comp_whiskerLeft F _ _ _ _ ξ
      (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_of_inverse _ _
        (ρ_ F).inv_hom_id (ρ_ F).hom_inv_id ξ)
      (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_sectionHom (tensorPow L r) s
        (h ξ hξ))
  · exact Or.inr hξ

/-- A morphism of modules can only shrink the nonvanishing locus of a global section. -/
private theorem nonvanishingLocus_app_subset {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (s : Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus N (φ.app ⊤ s) ⊆ Stacks.Ample.nonvanishingLocus M s := by
  intro x hx hs
  refine hx ?_
  rw [← Stacks.ModuleStalk.mapFun_Γgerm]
  exact Stacks.SectionProduct.mapFun_mem_maximalSmul φ x hs

/-- An isomorphism of modules preserves the nonvanishing locus of a global section. -/
private theorem nonvanishingLocus_iso_hom_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (s : Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus N (e.hom.app ⊤ s) = Stacks.Ample.nonvanishingLocus M s := by
  refine (nonvanishingLocus_app_subset e.hom s).antisymm ?_
  have h : e.inv.app ⊤ (e.hom.app ⊤ s) = s := by
    change ((e.hom ≫ e.inv).app ⊤) s = s
    rw [Iso.hom_inv_id]
    rfl
  conv_lhs => rw [← h]
  exact nonvanishingLocus_app_subset e.inv _

open Stacks.Ample in
/-- `L^{⊗ n}` in the monoidal structure of `X.Modules` is the `n`-th integer tensor power
`Stacks.Ample.tensorPowModule X L n`. -/
private theorem nonempty_tensorPow_iso_tensorPowModule (Y : Scheme.{u}) (L : Y.Modules)
    [IsInvertibleModule Y L] (n : ℕ) :
    Nonempty (tensorPow L n ≅ tensorPowModule Y L (n : ℤ)) := by
  induction n with
  | zero => exact ⟨(tensorPowModuleZeroIso Y L).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨(tensorIso e (tensorPowModuleOneIso Y L).symm : tensorPow L n ⊗ L ≅ _) ≪≫
      tensorPowModuleAddIso Y L (n : ℤ) 1 ≪≫ eqToIso (by push_cast; rfl)⟩

open MMP.Intersection (ProjSpace) in
/-- A very ample module, in the sense of `MMP.Intersection.IsVeryAmple`, is the pullback of
`𝒪(1)` along an immersion into projective space over `k`. -/
private theorem hasImmersionTwistOver_of_isVeryAmple {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {M N : X.Modules}
    (hva : MMP.Intersection.IsVeryAmple k M) (e : N ≅ M) :
    Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver (X ↘ Spec (.of k)) N := by
  obtain ⟨n, ι, hι, hover, ⟨e'⟩⟩ := hva
  refine ⟨n, ι ≫ (ProjSpace.isoProjectiveSpaceOver k n).hom, ?_, ?_, ⟨?_⟩⟩
  · have : IsClosedImmersion ι := hι
    infer_instance
  · rw [Category.assoc, ProjSpace.isoProjectiveSpaceOver_hom_fst, hover]
  · exact e ≪≫ e' ≪≫ (Scheme.Modules.pullback ι).mapIso
      (ProjSpace.twistOneIsoPullback k n).symm ≪≫
      (Scheme.Modules.pullbackComp ι (ProjSpace.isoProjectiveSpaceOver k n).hom).app _

/-- On a scheme proper over `k`, an ample line bundle in the sense of `MMP.Intersection.IsAmple`
is ample in the sense of `Stacks.Ample.IsAmple`. -/
private theorem stacksIsAmple_of_isAmple (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : MMP.Intersection.IsAmple k L) :
    Stacks.Ample.IsAmple X L := by
  obtain ⟨d, hd, hva⟩ := hL
  obtain ⟨eP⟩ := nonempty_tensorPow_iso_tensorPowModule X L d
  exact ((Stacks.AmpleRelativeFiniteType.tfae_six (X ↘ Spec (.of k)) L).out 5 1).1
    (⟨d, hd, hasImmersionTwistOver_of_isVeryAmple hva eP.symm⟩ : ∃ d : ℕ, 1 ≤ d ∧
      Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver (X ↘ Spec (.of k))
        (Stacks.Ample.tensorPowModule X L (d : ℤ)))

open Stacks.SectionsVanishingOnSubscheme Stacks.Chow.BertiniChain in
/-- For `r ≫ 0` there is a section of `L^{⊗r}` vanishing at the closed point `x` and at no point
of a given finite set `S ∌ x`. -/
private theorem eventually_exists_section_notMem_nonvanishingLocus (k : Type u) [Field k]
    [Infinite k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (hX : IsProjectiveMorphism (X ↘ Spec (.of k)))
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : MMP.Intersection.IsAmple k L)
    (x : X) (hx : IsClosed ({x} : Set X)) (S : Set X) (hS : S.Finite) (hxS : x ∉ S) :
    ∀ᶠ r : ℕ in Filter.atTop, ∃ s : MMP.Intersection.H0 k (tensorPow L r),
      x ∉ Stacks.Ample.nonvanishingLocus (tensorPow L r) s ∧
        ∀ ξ ∈ S, ξ ∈ Stacks.Ample.nonvanishingLocus (tensorPow L r) s := by
  have : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism _ hX
  have hample : Stacks.Ample.IsAmple X L := stacksIsAmple_of_isAmple k L hL
  set I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩
  obtain ⟨n₀, hn₀⟩ := exists_bound_generatesOffSupport k (X ↘ Spec (.of k)) I L hample
  rw [Filter.eventually_atTop]
  refine ⟨n₀.toNat, fun r hr => ?_⟩
  have hgen := hn₀ (r : ℤ) (by omega)
  have : Finite S := hS.to_subtype
  have hne : ∀ ξ : S, vanishingAtSubmodule k (X ↘ Spec (.of k)) I L (r : ℤ) ξ ≠ ⊤ := fun ξ =>
    vanishingAtSubmodule_ne_top k _ I L _ hgen fun h => hxS ((show (ξ : X) = x from h) ▸ ξ.2)
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top _ hne
  obtain ⟨e⟩ := nonempty_tensorPow_iso_tensorPowModule X L r
  let t : Γ(Stacks.Ample.tensorPowModule X L (r : ℤ), ⊤) :=
    ((v : Stacks.Bertini.globalSections k (X ↘ Spec (.of k))
      (Stacks.Ample.tensorPowModule X L (r : ℤ))) : _)
  have hnv : Stacks.Ample.nonvanishingLocus (tensorPow L r) (e.inv.app ⊤ t) =
      Stacks.Ample.nonvanishingLocus _ t :=
    nonvanishingLocus_iso_hom_app e.symm t
  refine ⟨e.inv.app ⊤ t, ?_, fun ξ hξ => ?_⟩
  · rw [hnv]
    exact fun h => h (Γgerm_mem_maximalSmul_of_mem_vanishingSections k _ I L _ x
      (Set.mem_singleton x) v)
  · rw [hnv]
    by_contra h
    exact hv ⟨ξ, hξ⟩ ((notMem_nvOpen_iff _ _ _).2 (not_not.mp h))

end SectionAvoidingAssociatedPoints

/-- At an associated point `y` of `F`, some nonzero element of `F_y` is killed by `𝔪_y`. -/
private theorem exists_ne_zero_forall_smul_eq_zero_of_isAssociatedPoint {X : Scheme.{u}}
    (F : X.Modules) {y : X} (hy : Stacks.Divisors.IsAssociatedPoint F y) :
    ∃ m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y, m ≠ 0 ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y), a • m = 0 := by
  obtain ⟨-, m, hm⟩ := hy
  refine ⟨m, ?_, fun a ha => ?_⟩
  · rintro rfl
    have h1 : (1 : X.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
      rw [← hm]
      refine Submodule.mem_colon.mpr fun p hp => ?_
      rw [Submodule.span_singleton_eq_bot.mpr rfl, SetLike.mem_coe, Submodule.mem_bot] at hp
      rw [hp, smul_zero]
      exact Submodule.zero_mem _
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · rw [← hm] at ha
    exact (Submodule.mem_bot _).mp (Submodule.mem_colon.mp ha m (Submodule.subset_span rfl))

/-- Step (i) of KM 5.72: under the hypotheses in dimension `n + 1`, a closed point is not an
associated point of `F`. -/
private theorem not_isAssociatedPoint_of_isClosed (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (F : X.Modules) (hF : Hyp k (n + 1) X L F) (x : X) (hx : IsClosed ({x} : Set X)) :
    ¬ Stacks.Divisors.IsAssociatedPoint F x := by
  intro hass
  have : IsNoetherian X := isNoetherian_of_isProjectiveMorphism k hF.1
  obtain ⟨r, hr⟩ := hF.2.2.2.2.exists
  have h0 := hr 0 (Nat.succ_pos n)
  set F' : X.Modules := F ⊗ (Stacks.Ample.tensorPowModule X L (-(r : ℤ)) : X.Modules)
  have hass' : Stacks.Divisors.IsAssociatedPoint F' x := by
    have := Stacks.EnriquesSeveriZariski.associatedPoints_twist L F (-(r : ℤ))
    have hmem : x ∈ Stacks.Divisors.associatedPoints F := hass
    rw [← this] at hmem
    exact hmem
  obtain ⟨m, hm0, hsmul⟩ := exists_ne_zero_forall_smul_eq_zero_of_isAssociatedPoint F' hass'
  obtain ⟨σ, hσ⟩ := exists_section_germ_ne_zero_of_forall_smul_eq_zero F' hx m hm0 hsmul
  have hsub : Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj F').obj.obj
      (Opposite.op ⊤)) :=
    (Sheaf.H.equiv₀ _ Limits.isTerminalTop).symm.injective.subsingleton
  apply hσ
  have : σ = 0 := Subsingleton.elim
      (α := ((SheafOfModules.toSheaf X.ringCatSheaf).obj F').obj.obj (Opposite.op ⊤)) σ 0
  rw [this, map_zero]

open TensorProduct in
/-- Multiplication by `c • e 1` on the right factor of `P ⊗ A`, where `u : A ≃ R` and
`e : R ≃ N`, is `c` times the equivalence `P ⊗ A ≃ P ⊗ N` induced by `u.trans e`. -/
private theorem lTensor_smul_eq {R : Type*} [CommRing R] {P A N : Type*} [AddCommGroup P]
    [Module R P] [AddCommGroup A] [Module R A] [AddCommGroup N] [Module R N] (u : A ≃ₗ[R] R)
    (e : R ≃ₗ[R] N) (c : R) (t : P ⊗[R] A) :
    LinearMap.lTensor P ((LinearMap.toSpanSingleton R N (c • e 1)).comp u.toLinearMap) t =
      c • ((LinearEquiv.lTensor P (u.trans e)) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, smul_add, ha, hb]
  | tmul p a =>
    simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.toSpanSingleton_apply, LinearEquiv.lTensor_tmul, LinearEquiv.trans_apply,
      TensorProduct.smul_tmul']
    rw [smul_tmul]
    congr 1
    rw [show u a = u a • (1 : R) by rw [smul_eq_mul, mul_one], map_smul, smul_comm, smul_eq_mul,
      mul_one]

/-- A stalk basis does not lie in `𝔪_y · M_y`. -/
private theorem notMem_maximalSmul_of_isStalkBasis {X : Scheme.{u}} {M : X.Modules} {y : X}
    {b : M.presheaf.stalk y} (hb : Stacks.Divisors.IsStalkBasis M y b) :
    b ∉ Stacks.ModuleStalk.maximalSmul M y := by
  intro h
  have h1 := Stacks.SheafOfModules.map_mem_ideal_smul_top _ hb.coord.toLinearMap h
  rw [LinearEquiv.coe_coe, hb.coord_self] at h1
  have h2 : (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
      (⊤ : Submodule (X.presheaf.stalk y) (X.presheaf.stalk y)) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    Submodule.smul_le.mpr fun r hr m _ => Ideal.mul_mem_right m _ hr
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr (h2 h1))

/-- On stalks, the kernel of `cokernel.π φ` is the range of `φ`. -/
theorem ker_stalkLinearMap_cokernel_π {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    LinearMap.ker (stalkLinearMap _ _ (cokernel.π φ) x) =
      LinearMap.range (stalkLinearMap _ _ φ x) := by
  ext n
  exact ⟨Stacks.GlueSquishFactor.exists_stalkLinearMap_eq_of_stalkLinearMap_cokernel_π_eq_zero
    φ x n, by
      rintro ⟨w, rfl⟩
      exact Stacks.GlueSquishFactor.stalkLinearMap_cokernel_π_stalkLinearMap φ x w⟩

open Stacks.EnriquesSeveriZariski in
/-- **The stalk of the cokernel of multiplication by a section.** Let `M` be invertible, `σ` a
global section of `M` vanishing at `x`, and `μ = u ≫ (1 ⊗ σ) : F ⟶ F ⊗ M` multiplication by `σ`
(with `u : F ⟶ F ⊗ 𝒪_X` bijective on stalks) injective on the stalk at `x`. Then there is a local
equation `c ∈ 𝔪_x` of `σ`, regular on `F_x`, with `(coker μ)_x ≅ F_x / c F_x`. -/
private theorem exists_linearEquiv_stalk_cokernel {X : Scheme.{u}} (F M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (σ : Γ(M, ⊤)) (x : X)
    (u : F ⟶ Scheme.Modules.tensorObj F (Stacks.Ample.unitModule X))
    (hu : Function.Bijective (stalkLinearMap _ _ u x))
    (hσx : x ∉ Stacks.Ample.nonvanishingLocus M σ)
    (hinj : Function.Injective
      (stalkLinearMap _ _ (u ≫ Scheme.Modules.tensorLeftMap F (sectionHom M σ)) x)) :
    ∃ c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      IsSMulRegular (F.presheaf.stalk x) c ∧
      Nonempty ((cokernel (u ≫ Scheme.Modules.tensorLeftMap F (sectionHom M σ))).presheaf.stalk x
        ≃ₗ[X.presheaf.stalk x] QuotSMulTop c (F.presheaf.stalk x)) := by
  set μ := u ≫ Scheme.Modules.tensorLeftMap F (sectionHom M σ) with hμdef
  haveI := (Stacks.InvertibleStalk.isInvertible_presheaf_iff M).2 ‹_›
  obtain ⟨V, hxV, e, hb⟩ := Stacks.InvertibleStalk.exists_germ_isStalkBasis M x
  set b := M.presheaf.germ V x hxV e
  set c := hb.coord ((M.presheaf.Γgerm x).hom σ)
  have hσ : (M.presheaf.Γgerm x).hom σ = c • b := (hb.smul_coord _).symm
  have hc : c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [Stacks.Ample.mem_nonvanishingLocus_iff, not_not, hσ,
      Stacks.ModuleStalk.smul_mem_maximalSmul_iff] at hσx
    rcases hσx with h | h
    · exact (IsLocalRing.mem_maximalIdeal c).mpr h
    · exact (notMem_maximalSmul_of_isStalkBasis hb h).elim
  set α := tensorStalkEquiv F (Stacks.Ample.unitModule X) x
  set β := tensorStalkEquiv F M x
  have hg : stalkLinearMap _ _ (sectionHom M σ) x =
      (LinearMap.toSpanSingleton _ _ (c • hb.linearEquiv 1)).comp
        (Stacks.Ample.unitStalkEquiv X x).toLinearMap := by
    refine LinearMap.ext fun z => ?_
    rw [stalkLinearMap_sectionHom, hσ, hb.linearEquiv_one]
    rfl
  set Φ : F.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (Scheme.Modules.tensorObj F M).presheaf.stalk x :=
    ((LinearEquiv.ofBijective _ hu).trans α).trans
      ((LinearEquiv.lTensor _ ((Stacks.Ample.unitStalkEquiv X x).trans hb.linearEquiv)).trans
        β.symm)
  have hμ : ∀ z, stalkLinearMap _ _ μ x z = c • Φ z := fun z => β.injective <| by
    rw [hμdef, Scheme.Modules.stalkLinearMap_comp, tensorStalkEquiv_tensorLeftMap, hg,
      lTensor_smul_eq, map_smul]
    congr 1
    exact (β.apply_symm_apply _).symm
  refine ⟨c, hc, fun f₁ f₂ h => hinj ?_, ?_⟩
  · rw [hμ, hμ, ← map_smul, ← map_smul]
    exact congrArg Φ h
  have hrange : LinearMap.range (stalkLinearMap _ _ μ x) =
      c • (⊤ : Submodule (X.presheaf.stalk x)
        ((Scheme.Modules.tensorObj F M).presheaf.stalk x)) := by
    ext n
    rw [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Φ z, Submodule.mem_top, (hμ z).symm⟩
    · rintro ⟨m, -, rfl⟩
      exact ⟨Φ.symm m, by rw [hμ, Φ.apply_symm_apply]⟩
  exact ⟨((LinearMap.quotKerEquivOfSurjective _
    (Stacks.GlueSquishFactor.surjective_stalkLinearMap_cokernel_π μ x)).symm.trans
      (Submodule.quotEquivOfEq _ _ ((ker_stalkLinearMap_cokernel_π μ x).trans hrange))).trans
        (QuotSMulTop.congr c Φ.symm)⟩

/-- Sheaf cohomology of isomorphic modules: `Subsingleton` transfers. -/
private theorem subsingleton_sheafCohomology_of_iso {X : Scheme.{u}} {A B : X.Modules}
    (e : A ≅ B) (i : ℕ)
    (h : Subsingleton (Sheaf.H.{u}
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj A) i)) :
    Subsingleton (Sheaf.H.{u}
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj B) i) :=
  ((Sheaf.functorH.{u} (Opens.grothendieckTopology X) i).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)).addCommGroupIsoToAddEquiv.toEquiv
      |>.subsingleton_congr |>.1 h

/-- On a scheme over `k`, the long exact sequence: if `H^i(X₂) = 0` and `H^{i+1}(X₁) = 0` then
`H^i(X₃) = 0`, for a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of `𝒪_X`-modules. -/
private theorem subsingleton_sheafCohomology_X₃ (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {S : ShortComplex X.Modules} (hS : S.ShortExact) (i : ℕ)
    (h₂ : Subsingleton (Sheaf.H.{u}
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂) i))
    (h₁ : Subsingleton (Sheaf.H.{u}
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₁) (i + 1))) :
    Subsingleton (Sheaf.H.{u}
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃) i) := by
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence k (X ↘ Spec (.of k)) hS
  have h₂' : Subsingleton (cohomologyOverField k (X ↘ Spec (.of k)) S.X₂ i) :=
    (MMP.Cohomology.subsingleton_sheafH_iff _ _).1 h₂
  have h₁' : Subsingleton (cohomologyOverField k (X ↘ Spec (.of k)) S.X₁ (i + 1)) :=
    (MMP.Cohomology.subsingleton_sheafH_iff _ _).1 h₁
  have h₃ : ∀ z : cohomologyOverField k (X ↘ Spec (.of k)) S.X₃ i, z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (hgd i z).mp (Subsingleton.elim _ _)
    rw [← hw, Subsingleton.elim w 0, map_zero]
  haveI : Subsingleton (cohomologyOverField k (X ↘ Spec (.of k)) S.X₃ i) :=
    ⟨fun a b => (h₃ a).trans (h₃ b).symm⟩
  exact (MMP.Cohomology.subsingleton_sheafH_iff _ _).2 this

/-- **Step (ii) of KM 5.72.** If `μ : F ⟶ F ⊗ M` is a monomorphism with `M ≅ L^{r}`, and
`H^i(F ⊗ L^{-j}) = 0` for `i < n + 1` and `j ≫ 0`, then `H^i(coker μ ⊗ L^{-j}) = 0` for `i < n`
and `j ≫ 0`. -/
private theorem eventually_subsingleton_sheafCohomology_cokernel (k : Type u) [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n r : ℕ) (F M : X.Modules)
    (eM : M ≅ Stacks.Ample.tensorPowModule X L (r : ℤ)) (μ : F ⟶ F ⊗ M) (hμ : Mono μ)
    (hvan : ∀ᶠ j : ℕ in Filter.atTop, ∀ i < n + 1,
      Subsingleton (Sheaf.H.{u}
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (F ⊗ (Stacks.Ample.tensorPowModule X L (-(j : ℤ)) : X.Modules) : X.Modules)) i)) :
    ∀ᶠ j : ℕ in Filter.atTop, ∀ i < n,
      Subsingleton (Sheaf.H.{u}
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (cokernel μ ⊗ (Stacks.Ample.tensorPowModule X L (-(j : ℤ)) : X.Modules) :
            X.Modules)) i) := by
  have hS : (ShortComplex.mk μ (cokernel.π μ) (cokernel.condition μ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact μ) hμ inferInstance
  filter_upwards [hvan, (Filter.tendsto_sub_atTop_nat r).eventually hvan,
    Filter.eventually_ge_atTop r] with j hj hjr hrj i hi
  have hS' := Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight X
    (Stacks.Ample.tensorPowModule X L (-(j : ℤ))) hS
  refine subsingleton_sheafCohomology_X₃ k hS' i ?_ (hj (i + 1) (by omega))
  have hz : (r : ℤ) + -(j : ℤ) = -((j - r : ℕ) : ℤ) := by omega
  have e : (F ⊗ M) ⊗ Stacks.Ample.tensorPowModule X L (-(j : ℤ)) ≅
      F ⊗ Stacks.Ample.tensorPowModule X L (-((j - r : ℕ) : ℤ)) :=
    α_ _ _ _ ≪≫ whiskerLeftIso F (whiskerRightIso eM _ ≪≫
      Stacks.Ample.tensorPowModuleAddIso X L (r : ℤ) (-(j : ℤ)) ≪≫ eqToIso (by rw [hz]))
  exact subsingleton_sheafCohomology_of_iso e.symm i (hjr i (by omega))

/-- A monomorphism of `𝒪_X`-modules is injective on stalks: the stalk functor is exact. -/
private theorem injective_stalkLinearMap_of_mono {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G)
    (hf : Mono f) (x : X) : Function.Injective (stalkLinearMap F G f x) := by
  have hm : @Mono (SheafOfModules.{u} X.ringCatSheaf) _ F G f :=
    ⟨fun g h e => hf.right_cancellation g h e⟩
  have : Mono ((Scheme.Modules.stalkFunctor X x).map f) :=
    @Functor.map_mono _ _ _ _ (Scheme.Modules.stalkFunctor X x) _ _ _ f hm
  exact (ModuleCat.mono_iff_injective _).mp this

section Purity

open MMP.Foundations

set_option backward.isDefEq.respectTransparency false in
private theorem fromSpecStalk_stalkSpecializationPrime {X : Scheme.{u}} {x y : X} (h : y ⤳ x) :
    X.fromSpecStalk x (⟨stalkSpecializationPrime h, Ideal.comap_isPrime _ _⟩ :
      PrimeSpectrum (X.presheaf.stalk x)) = y := by
  have e : (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk x)
      (IsLocalRing.closedPoint (X.presheaf.stalk y)) = y := by
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk h, Scheme.fromSpecStalk_closedPoint]
  rw [Scheme.Hom.comp_apply] at e
  exact e

private theorem specializes_iff_stalkSpecializationPrime_le {X : Scheme.{u}} {x y y' : X}
    (h : y ⤳ x) (h' : y' ⤳ x) :
    y ⤳ y' ↔ stalkSpecializationPrime h ≤ stalkSpecializationPrime h' := by
  have e := (X.fromSpecStalk x).isEmbedding.specializes_iff
    (x := (⟨stalkSpecializationPrime h, Ideal.comap_isPrime _ _⟩ :
      PrimeSpectrum (X.presheaf.stalk x)))
    (y := (⟨stalkSpecializationPrime h', Ideal.comap_isPrime _ _⟩ :
      PrimeSpectrum (X.presheaf.stalk x)))
  rw [fromSpecStalk_stalkSpecializationPrime h, fromSpecStalk_stalkSpecializationPrime h'] at e
  exact e.trans (PrimeSpectrum.le_iff_specializes _ _).symm

/-- **A local equation of a section of an invertible module.** For a global section `σ` of an
invertible `M` and a point `ξ`, there is `c ∈ 𝒪_{X,ξ}` such that `σ` vanishes at a generization
`y` of `ξ` exactly when `c` lies in the prime of `𝒪_{X,ξ}` attached to `y`. -/
private theorem exists_forall_mem_nonvanishingLocus_iff {X : Scheme.{u}} (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (σ : Γ(M, ⊤)) (ξ : X) :
    ∃ c : X.presheaf.stalk ξ, ∀ (y : X) (h : y ⤳ ξ),
      y ∈ Stacks.Ample.nonvanishingLocus M σ ↔ c ∉ stalkSpecializationPrime h := by
  haveI := (Stacks.InvertibleStalk.isInvertible_presheaf_iff M).2 ‹_›
  obtain ⟨V, hξV, e, he⟩ := Stacks.Divisors.isTrivializedNear_of_isInvertible M ξ
  have hb := he ξ hξV
  refine ⟨hb.coord ((M.presheaf.Γgerm ξ).hom σ), fun y h => ?_⟩
  set c := hb.coord ((M.presheaf.Γgerm ξ).hom σ)
  have hyV : y ∈ V := h.mem_open V.isOpen hξV
  letI := stalkModule M ξ
  letI := stalkModule M y
  have hσ : (M.presheaf.Γgerm y).hom σ =
      X.presheaf.stalkSpecializes h c • M.presheaf.germ V y hyV e := by
    have h1 : (M.presheaf.Γgerm y).hom σ =
        M.presheaf.stalkSpecializes h ((M.presheaf.Γgerm ξ).hom σ) :=
      (germ_stalkSpecializes_apply M (TopologicalSpace.Opens.mem_top ξ) h σ).symm
    rw [h1, ← hb.smul_coord ((M.presheaf.Γgerm ξ).hom σ),
      Stacks.ModuleStalkSpecialization.stalkSpecializes_smul,
      germ_stalkSpecializes_apply M hξV h e]
  rw [Stacks.Ample.mem_nonvanishingLocus_iff, hσ, Stacks.ModuleStalk.smul_mem_maximalSmul_iff,
    stalkSpecializationPrime, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have := notMem_maximalSmul_of_isStalkBasis (he y hyV)
  tauto

private theorem notMem_minimalPrimes_sup_span_singleton_of_lt_of_lt {R : Type*} [CommRing R]
    [IsNoetherianRing R] {P Q N : Ideal R} [hP : P.IsPrime] [hQ : Q.IsPrime] [hN : N.IsPrime]
    (hPQ : P < Q) (hQN : Q < N) (c : R) : N ∉ (P ⊔ Ideal.span {c}).minimalPrimes := by
  intro hmin
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hs : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hpr : ∀ J : Ideal R, J.IsPrime → P ≤ J → (J.map (Ideal.Quotient.mk P)).IsPrime :=
    fun J hJ hPJ => Ideal.map_isPrime_of_surjective hs (by rw [hker]; exact hPJ)
  have hcm : ∀ J : Ideal R, P ≤ J →
      (J.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = J := fun J hPJ => by
    rw [Ideal.comap_map_of_surjective' _ hs, hker, sup_eq_left.mpr hPJ]
  haveI := hpr P hP le_rfl
  haveI := hpr Q hQ hPQ.le
  haveI := hpr N hN (hPQ.le.trans hQN.le)
  let a : PrimeSpectrum (R ⧸ P) := ⟨P.map (Ideal.Quotient.mk P), inferInstance⟩
  let b : PrimeSpectrum (R ⧸ P) := ⟨Q.map (Ideal.Quotient.mk P), inferInstance⟩
  let d : PrimeSpectrum (R ⧸ P) := ⟨N.map (Ideal.Quotient.mk P), inferInstance⟩
  have hlt : ∀ {J K : Ideal R}, P ≤ J → P ≤ K → J < K →
      J.map (Ideal.Quotient.mk P) < K.map (Ideal.Quotient.mk P) := by
    intro J K hJ hK hJK
    refine lt_of_le_of_ne (Ideal.map_mono hJK.le) fun h => hJK.ne ?_
    rw [← hcm J hJ, ← hcm K hK, h]
  have hab : a < b := hlt le_rfl hPQ.le hPQ
  have hbd : b < d := hlt hPQ.le (hPQ.le.trans hQN.le) hQN
  have h2 : (2 : ℕ∞) ≤ Order.height d := by
    have e1 := Order.height_add_one_le hab
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.height a + 1 + 1 := by
        gcongr
        exact zero_le
      _ ≤ Order.height b + 1 := by gcongr
      _ ≤ Order.height d := Order.height_add_one_le hbd
  rw [show (N.map (Ideal.Quotient.mk P)).height = Order.height d from
    PrimeSpectrum.height_eq_orderHeight d] at h1
  exact absurd (h2.trans h1) (by norm_num)

/-- **Krull's principal ideal theorem along a section.** On a locally Noetherian scheme, let `σ`
be a section of an invertible module vanishing at `ξ`, and `η` a generization of `ξ` such that `ξ`
is the only point between `η` and `ξ` at which `σ` vanishes. Then there is no chain `ξ < a < η`
of specializations. -/
private theorem false_of_specializes_chain {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (σ : Γ(M, ⊤)) {ξ a η : X}
    (ha : a ⤳ ξ) (hηa : η ⤳ a) (hne₁ : a ≠ ξ) (hne₂ : η ≠ a)
    (hξ : ξ ∉ Stacks.Ample.nonvanishingLocus M σ)
    (hmin : ∀ y, η ⤳ y → y ⤳ ξ → y ∉ Stacks.Ample.nonvanishingLocus M σ → y = ξ) : False := by
  obtain ⟨c, hc⟩ := exists_forall_mem_nonvanishingLocus_iff M σ ξ
  have hηξ := hηa.trans ha
  have hrefl : ξ ⤳ ξ := specializes_refl ξ
  haveI : (stalkSpecializationPrime hηξ).IsPrime := Ideal.comap_isPrime _ _
  haveI : (stalkSpecializationPrime ha).IsPrime := Ideal.comap_isPrime _ _
  haveI : (stalkSpecializationPrime hrefl).IsPrime := Ideal.comap_isPrime _ _
  have hPQ : stalkSpecializationPrime hηξ < stalkSpecializationPrime ha := by
    refine lt_of_le_of_ne ((specializes_iff_stalkSpecializationPrime_le hηξ ha).mp hηa)
      fun h => hne₂
        (hηa.antisymm ((specializes_iff_stalkSpecializationPrime_le ha hηξ).mpr h.ge)).eq
  have hQN : stalkSpecializationPrime ha < stalkSpecializationPrime hrefl := by
    refine lt_of_le_of_ne ((specializes_iff_stalkSpecializationPrime_le ha hrefl).mp ha)
      fun h => hne₁
        (ha.antisymm ((specializes_iff_stalkSpecializationPrime_le hrefl ha).mpr h.ge)).eq
  refine notMem_minimalPrimes_sup_span_singleton_of_lt_of_lt hPQ hQN c ?_
  have hcN : c ∈ stalkSpecializationPrime hrefl := by
    by_contra h
    exact hξ ((hc ξ hrefl).mpr h)
  refine ⟨⟨inferInstance, sup_le ((specializes_iff_stalkSpecializationPrime_le hηξ hrefl).mp hηξ)
    ((Ideal.span_singleton_le_iff_mem _).mpr hcN)⟩, fun q ⟨hq, hle⟩ _ => ?_⟩
  obtain ⟨y, h, rfl⟩ := exists_specializes_stalkSpecializationPrime_eq ξ q
  have hηy : η ⤳ y :=
    (specializes_iff_stalkSpecializationPrime_le hηξ h).mpr (le_sup_left.trans hle)
  have hcy : c ∈ stalkSpecializationPrime h :=
    hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self c))
  have hy : y ∉ Stacks.Ample.nonvanishingLocus M σ := fun hy => (hc y h).mp hy hcy
  obtain rfl := hmin y hηy h hy
  exact le_rfl

/-- An irreducible component `Z` of a closed subset `A` of a scheme has a generic point `ξ ∈ A`
which has no proper generization inside `A`, and `dim Z = height ξ`. -/
private theorem exists_genericPoint_of_mem_irreducibleComponents {X : Scheme.{u}} {A : Set X}
    (hA : IsClosed A) {Z : Set A} (hZ : Z ∈ irreducibleComponents A) :
    ∃ ξ ∈ A, (∀ y ∈ A, y ⤳ ξ → y = ξ) ∧ (∀ z ∈ Z, ξ ⤳ (z : X)) ∧
      topologicalKrullDim Z = (Order.height ξ : WithBot ℕ∞) := by
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hZi : IsIrreducible Z := hZ.1
  have hZ'c : IsClosed (Subtype.val '' Z : Set X) :=
    hA.isClosedEmbedding_subtypeVal.isClosedMap _ hZc
  have hZ'i : IsIrreducible (Subtype.val '' Z : Set X) :=
    hZi.image _ continuous_subtype_val.continuousOn
  have hgen := hZ'i.isGenericPoint_genericPoint_closure
  rw [hZ'c.closure_eq] at hgen
  set ξ := hZ'i.genericPoint
  obtain ⟨ξA, hξZ, hξA⟩ := hgen.mem
  have hspec : ∀ z ∈ Z, ξ ⤳ (z : X) := fun z hz => hgen.specializes ⟨z, hz, rfl⟩
  refine ⟨ξ, hξA ▸ ξA.2, fun y hy hyξ => ?_, hspec, ?_⟩
  · have hsub : Z ⊆ closure {(⟨y, hy⟩ : A)} := fun z hz =>
      specializes_iff_mem_closure.mp ((subtype_specializes_iff _ _).mpr (hyξ.trans (hspec z hz)))
    have heq := hZ.eq_of_le isIrreducible_singleton.closure hsub
    have hyZ : (⟨y, hy⟩ : A) ∈ Z := heq ▸ subset_closure rfl
    exact (hyξ.antisymm (hspec _ hyZ)).eq
  · have he : Topology.IsEmbedding (Subtype.val ∘ Subtype.val : Z → X) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    rw [IsHomeomorph.topologicalKrullDim_eq _ he.toHomeomorph.isHomeomorph, Set.range_comp,
      Subtype.range_coe, ← hgen.def]
    exact AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height ξ

/-- **Dimension drop along a section** (KM 5.72, step (iii)): on a scheme locally of finite type
over a field, if every irreducible component of the closed set `S` has dimension `n + 1` and the
section `σ` vanishes at none of their generic points, then every irreducible component of
`S ∩ (σ = 0)` has dimension `n`. -/
private theorem forall_topologicalKrullDim_inter_eq (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsLocallyNoetherian X]
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (σ : Γ(M, ⊤)) (n : ℕ) {S : Set X}
    (hS : IsClosed S) (hNV : IsOpen (Stacks.Ample.nonvanishingLocus M σ))
    (hF : ∀ W ∈ irreducibleComponents S, topologicalKrullDim W = ((n + 1 : ℕ) : WithBot ℕ∞))
    (hgen : ∀ η ∈ S, (∀ y ∈ S, y ⤳ η → y = η) → η ∈ Stacks.Ample.nonvanishingLocus M σ) :
    ∀ Z ∈ irreducibleComponents (S ∩ (Stacks.Ample.nonvanishingLocus M σ)ᶜ : Set X),
      topologicalKrullDim Z = (n : WithBot ℕ∞) := by
  intro Z hZ
  have hT : IsClosed (S ∩ (Stacks.Ample.nonvanishingLocus M σ)ᶜ) := hS.inter hNV.isClosed_compl
  obtain ⟨ξ, ⟨hξS, hξN⟩, hmaxξ, -, hdimZ⟩ := exists_genericPoint_of_mem_irreducibleComponents hT hZ
  obtain ⟨W, hW, hξW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    {(⟨ξ, hξS⟩ : S)} isIrreducible_singleton
  obtain ⟨η, hηS, hmaxη, hηspec, hdimW⟩ := exists_genericPoint_of_mem_irreducibleComponents hS hW
  have hηξ : η ⤳ ξ := hηspec _ (hξW rfl)
  have hηN := hgen η hηS hmaxη
  have hhη : Order.height η = ((n + 1 : ℕ) : ℕ∞) :=
    WithBot.coe_inj.mp (hdimW.symm.trans (hF W hW))
  have hle : ξ ≤ η := Scheme.le_iff_specializes.mpr hηξ
  obtain ⟨hcat, -⟩ := MMP.height_eq_height_add_coheight_Iic k hle
  have hne : ξ ≠ η := fun h => hξN (h ▸ hηN)
  have hc : Order.coheight (⟨ξ, hle⟩ : Set.Iic η) = 1 := by
    refine le_antisymm ?_ ?_
    · by_contra hc
      have h2 : ((2 : ℕ) : ℕ∞) ≤ Order.coheight (⟨ξ, hle⟩ : Set.Iic η) :=
        Order.add_one_le_of_lt (lt_of_not_ge hc)
      obtain ⟨p, hp0, hpl⟩ := Order.exists_series_of_le_coheight _ h2
      have h01 : p ⟨0, by omega⟩ < p ⟨1, by omega⟩ := p.strictMono (Fin.mk_lt_mk.mpr (by omega))
      have h12 : p ⟨1, by omega⟩ < p ⟨2, by omega⟩ := p.strictMono (Fin.mk_lt_mk.mpr (by omega))
      have hp0' : (p ⟨0, by omega⟩ : X) = ξ := by
        rw [Fin.zero_eta]
        exact congrArg Subtype.val hp0
      set a : X := (p ⟨1, by omega⟩ : X)
      have hξa : ξ < a := hp0' ▸ h01
      have haη : a < η := lt_of_lt_of_le h12 (p ⟨2, by omega⟩).2
      refine false_of_specializes_chain M σ (Scheme.le_iff_specializes.mp hξa.le)
        (Scheme.le_iff_specializes.mp haη.le) hξa.ne' haη.ne' hξN ?_
      intro y hηy hyξ hyN
      have hyS : y ∈ S := hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηS)
        (specializes_iff_mem_closure.mp hηy)
      exact hmaxξ y ⟨hyS, hyN⟩ hyξ
    · rw [Order.one_le_iff_pos, Order.coheight_pos]
      intro hmax
      have : (⟨ξ, hle⟩ : Set.Iic η) < ⟨η, Set.mem_Iic.mpr (le_refl η)⟩ :=
        lt_of_le_not_ge hle fun h =>
        hne ((Scheme.le_iff_specializes.mp h).antisymm hηξ).eq
      exact hmax.not_lt this
  rw [hc, hhη] at hcat
  have hξh : Order.height ξ = (n : ℕ∞) := by
    have h1 : ((n : ℕ∞) + 1) = Order.height ξ + 1 := by exact_mod_cast hcat
    exact (ENat.add_left_injective_of_ne_top ENat.one_ne_top h1).symm
  rw [hdimZ, hξh]
  rfl

/-- An associated point lies in the support. -/
private theorem nontrivial_stalk_of_isAssociatedPoint {X : Scheme.{u}} (F : X.Modules) {y : X}
    (hy : Stacks.Divisors.IsAssociatedPoint F y) :
    Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) := by
  obtain ⟨m, hm0, -⟩ := exists_ne_zero_forall_smul_eq_zero_of_isAssociatedPoint F hy
  exact ⟨⟨m, 0, hm0⟩⟩

/-- A point of the support of a coherent module with no proper generization in the support (the
generic point of an irreducible component) is an associated point. -/
private theorem isAssociatedPoint_of_maximal {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] {η : X}
    (hη : Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf η))
    (hmax : ∀ y, Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) →
      y ⤳ η → y = η) :
    Stacks.Divisors.IsAssociatedPoint F η := by
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty (X.presheaf.stalk η)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf η)
  rw [associatedPrimes_stalk_eq] at hp
  obtain ⟨y, h, hy, -⟩ := hp
  obtain rfl := hmax y (nontrivial_stalk_of_isAssociatedPoint F hy) h
  exact hy

open Stacks.EnriquesSeveriZariski in
/-- The support of `coker(u ≫ (1 ⊗ σ))` is `Supp F ∩ (σ = 0)`. -/
private theorem setOf_nontrivial_stalk_cokernel {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    (σ : Γ(M, ⊤)) (u : F ⟶ Scheme.Modules.tensorObj F (Stacks.Ample.unitModule X))
    (hu : ∀ y, Function.Bijective (stalkLinearMap _ _ u y))
    (hmono : Mono (u ≫ Scheme.Modules.tensorLeftMap F (sectionHom M σ))) :
    {y : X | Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u})
        (cokernel (u ≫ Scheme.Modules.tensorLeftMap F (sectionHom M σ))).val.presheaf y)} =
      {y : X | Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y)} ∩
        (Stacks.Ample.nonvanishingLocus M σ)ᶜ := by
  set μ := u ≫ Scheme.Modules.tensorLeftMap F (sectionHom M σ)
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  by_cases hy : y ∈ Stacks.Ample.nonvanishingLocus M σ
  · simp only [hy, not_true_eq_false, and_false, iff_false, not_nontrivial_iff_subsingleton]
    have hbij : Function.Surjective (stalkLinearMap _ _ μ y) := by
      have h := bijective_stalkLinearMap_comp _ _ y (hu y)
        (bijective_stalkLinearMap_tensorLeftMap F (sectionHom M σ) y
          (bijective_stalkLinearMap_sectionHom M σ hy))
      exact h.2
    refine ⟨fun g₁ g₂ => ?_⟩
    have h0 : ∀ g : (cokernel μ).presheaf.stalk y, g = 0 := by
      intro g
      obtain ⟨n, rfl⟩ := Stacks.GlueSquishFactor.surjective_stalkLinearMap_cokernel_π μ y g
      obtain ⟨w, rfl⟩ := hbij n
      exact Stacks.GlueSquishFactor.stalkLinearMap_cokernel_π_stalkLinearMap μ y w
    exact (h0 g₁).trans (h0 g₂).symm
  · simp only [hy, not_false_eq_true, and_true]
    obtain ⟨c, hc, -, ⟨e⟩⟩ := exists_linearEquiv_stalk_cokernel F M σ y u (hu y) hy
      (injective_stalkLinearMap_of_mono _ hmono y)
    have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType (M := F)
    have : Module.Finite (X.presheaf.stalk y) (F.presheaf.stalk y) :=
      SheafOfModules.finite_stalk X.sheaf F y
    constructor
    · intro hG
      by_contra hF
      rw [not_nontrivial_iff_subsingleton] at hF
      haveI : Subsingleton (F.presheaf.stalk y) := hF
      haveI : Nontrivial ((cokernel μ).presheaf.stalk y) := hG
      have : Subsingleton (QuotSMulTop c (F.presheaf.stalk y)) :=
        (Submodule.mkQ_surjective _).subsingleton
      exact not_nontrivial_iff_subsingleton.mpr e.toEquiv.subsingleton ‹_›
    · intro hF
      have : Nontrivial (F.presheaf.stalk y) := hF
      have := nontrivial_quotSMulTop_of_mem_maximalIdeal (F.presheaf.stalk y) hc
      exact e.toEquiv.nontrivial

open Stacks.EnriquesSeveriZariski in
/-- Step (iii) of KM 5.72: if `Supp F` is pure of dimension `n + 1` and `σ` vanishes at no
associated point of `F`, every irreducible component of `Supp (coker (u ≫ (1 ⊗ σ)))` has
dimension `n`. -/
private theorem forall_topologicalKrullDim_supp_cokernel_eq (k : Type u) [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] (hX : IsProjectiveMorphism (X ↘ Spec (.of k)))
    (n : ℕ) (F : X.Modules) [SheafOfModules.IsCoherent F]
    (hF : ∀ Z ∈ irreducibleComponents
        {x : X | Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)},
      topologicalKrullDim Z = ((n + 1 : ℕ) : WithBot ℕ∞))
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (σ : Γ(M, ⊤))
    (hσ : ∀ ξ, Stacks.Divisors.IsAssociatedPoint F ξ → ξ ∈ Stacks.Ample.nonvanishingLocus M σ)
    (u : F ⟶ Scheme.Modules.tensorObj F (Stacks.Ample.unitModule X))
    (hu : ∀ y, Function.Bijective (stalkLinearMap _ _ u y))
    (hmono : Mono (u ≫ Scheme.Modules.tensorLeftMap F (sectionHom M σ))) :
    ∀ Z ∈ irreducibleComponents {y : X | Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u})
        (cokernel (u ≫ Scheme.Modules.tensorLeftMap F (sectionHom M σ))).val.presheaf y)},
      topologicalKrullDim Z = (n : WithBot ℕ∞) := by
  have : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism _ hX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  rw [setOf_nontrivial_stalk_cokernel F M σ u hu hmono]
  have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType (M := F)
  have hSF : IsClosed
      {y : X | Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y)} := by
    have heq : {y : X | Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y)} =
        SheafOfModules.supp F := by
      ext y
      exact nontrivial_iff_exists_ne 0
    exact heq ▸ SheafOfModules.isClosed_supp (R := X.ringCatSheaf) F
  refine forall_topologicalKrullDim_inter_eq k M σ n hSF
    (Stacks.NonvanishingOpen.isOpen_nonvanishingLocus X M σ) hF fun η hη hmax => ?_
  exact hσ η (isAssociatedPoint_of_maximal F hη hmax)

end Purity

open Stacks.EnriquesSeveriZariski in
/-- The hypersurface section of the inductive step, on `X` itself: at a closed point `x` there is
`c ∈ 𝔪_x` regular on `F_x` and a sheaf `G` (the cokernel of multiplication by a section of
`L^{r}` vanishing at `x` and at no associated point of `F`) satisfying the hypotheses in
dimension `n`, with `G_x ≅ F_x / c F_x`. -/
private theorem exists_quotient_hyp (k : Type u) [Field k] [Infinite k] (n : ℕ)
    {X : Scheme.{u}} [X.Over (Spec (.of k))] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (F : X.Modules) (hF : Hyp k (n + 1) X L F)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      IsSMulRegular (F.presheaf.stalk x) c ∧ ∃ G : X.Modules, Hyp k n X L G ∧
        Nonempty (G.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
          QuotSMulTop c (F.presheaf.stalk x)) := by
  have hass := not_isAssociatedPoint_of_isClosed k n L F hF x hx
  obtain ⟨hX, hL, hcoh, hdim, hvan⟩ := hF
  have : IsNoetherian X := isNoetherian_of_isProjectiveMorphism k hX
  obtain ⟨r, s, hsx, hsAss⟩ := (eventually_exists_section_notMem_nonvanishingLocus k hX
    L hL x hx (Stacks.Divisors.associatedPoints F) (MMP.Foundations.finite_associatedPoints F)
    hass).exists
  haveI : Stacks.Ample.IsInvertibleModule X (MMP.Intersection.Scheme.Modules.tensorPow L r) :=
    isInvertibleModule_tensorPow L r
  have hmono := mono_mul_of_forall_isAssociatedPoint_mem_nonvanishingLocus k F L r s
    hsAss
  let M := MMP.Intersection.Scheme.Modules.tensorPow L r
  let u : F ⟶ Scheme.Modules.tensorObj F (Stacks.Ample.unitModule X) := (ρ_ F).inv
  have hμ : (ρ_ F).inv ≫ F ◁ (SheafOfModules.unitHomEquiv
      (MMP.Intersection.Scheme.Modules.tensorPow L r)).symm s.toSections =
      u ≫ Scheme.Modules.tensorLeftMap F (sectionHom M s) := by
    congr 1
    exact whiskerLeft_eq_tensorLeftMap F _ _ _
  have hmono' : Mono (u ≫ Scheme.Modules.tensorLeftMap F (sectionHom M s)) := hμ ▸ hmono
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have hu : ∀ y, Function.Bijective (stalkLinearMap _ _ u y) := fun y =>
    bijective_stalkLinearMap_of_inverse _ _ (ρ_ F).inv_hom_id (ρ_ F).hom_inv_id y
  obtain ⟨c, hc, hreg, ⟨e⟩⟩ := exists_linearEquiv_stalk_cokernel F M s x u (hu x) hsx
    (injective_stalkLinearMap_of_mono _ hmono' x)
  obtain ⟨eM⟩ := nonempty_tensorPow_iso_tensorPowModule X L r
  have : (Scheme.Modules.tensorObj F M).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X F M
  refine ⟨c, hc, hreg, _, ⟨hX, hL, AlgebraicGeometry.isCoherent_cokernel _, ?_, ?_⟩, ⟨e⟩⟩
  · exact forall_topologicalKrullDim_supp_cokernel_eq k hX n F hdim M s hsAss u hu hmono'
  · exact eventually_subsingleton_sheafCohomology_cokernel k L n r F M eM _ hmono' hvan

/-- The inductive step of KM 5.72: under `Hyp k (n + 1)`, the stalk at a closed point is
Cohen–Macaulay. -/
private theorem isCMModule_stalk_of_succ (k : Type u) [Field k] [Infinite k] (n : ℕ)
    (ih : ∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))] (M : Y.Modules)
      [Stacks.Ample.IsInvertibleModule Y M] (G : Y.Modules), Hyp k n Y M G → IsCMSheaf G)
    {X : Scheme.{u}} [X.Over (Spec (.of k))] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (F : X.Modules) (hF : Hyp k (n + 1) X L F)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsCMModule (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) := by
  obtain ⟨c, hc, hreg, G, hG, ⟨e⟩⟩ := exists_quotient_hyp k n L F hF x hx
  have : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism _ hF.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := hF.2.2.1
  have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType (M := F)
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    SheafOfModules.finite_stalk X.sheaf F x
  exact (isCMModule_quotSMulTop_iff.{u, u, u, u} hc hreg).1.mp
    (isCMModule_of_linearEquiv e (ih X L G hG x))

private theorem isCMSheaf_of_hyp (k : Type u) [Field k] [Infinite k] (n : ℕ) :
    ∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] (L : X.Modules)
      [Stacks.Ample.IsInvertibleModule X L] (F : X.Modules), Hyp k n X L F → IsCMSheaf F := by
  induction n with
  | zero =>
    intro X _ L _ F hF
    exact isCMModule_stalk_of_zero k L F hF
  | succ n ih =>
    intro X _ L _ F hF
    have := hF.2.2.1
    exact isCMSheaf_of_forall_isClosed k hF.1 F
      (isCMModule_stalk_of_succ k n ih L F hF)

/-- **Vanishing of negative twists implies Cohen–Macaulay** (Kollár–Mori, Cor. 5.72). Let `X`
be projective over `k`, `L` an ample invertible sheaf and `F` a coherent sheaf whose support
`{x | F_x ≠ 0}` is pure of dimension `n`. If `H^i(X, F ⊗ L^{-r}) = 0` for every `i < n` and all
large `r`, then `F` is a Cohen–Macaulay sheaf. -/
@[mmp "prop_km5c_negative_twist_vanishing_implies_cm"]
public theorem isCMSheaf_of_eventually_subsingleton_sheafCohomology_tensorPowModule_neg
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (hX : IsProjectiveMorphism (X ↘ Spec (.of k)))
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : MMP.Intersection.IsAmple k L)
    (n : ℕ) (F : X.Modules) [SheafOfModules.IsCoherent F]
    (hF : ∀ Z ∈ irreducibleComponents
        {x : X | Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)},
      topologicalKrullDim Z = n)
    (hvan : ∀ᶠ r : ℕ in Filter.atTop, ∀ i < n,
      Subsingleton (Sheaf.H.{u}
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (F ⊗ (Stacks.Ample.tensorPowModule X L (-(r : ℤ)) : X.Modules) : X.Modules)) i)) :
    IsCMSheaf F :=
  isCMSheaf_of_hyp k n X L F ⟨hX, hL, ‹_›, hF, hvan⟩

end MMP.Mori

end
