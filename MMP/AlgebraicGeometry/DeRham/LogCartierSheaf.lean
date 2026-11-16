module

public import StacksFrontier.AlgebraicGeometry.SheafComplexLocality.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# The sheaf-level inverse Cartier isomorphism: the local criterion

Let `R` be a sheaf of rings on a topological space `X`, `C` a cochain complex of sheaves of
`R`-modules, `M` a sheaf of `R`-modules and `c : M ⟶ ℋ^q(C)` a morphism into the `q`-th
cohomology sheaf of `C`. Suppose `c` is described locally by a relation between sections `s` of
`M` and sections `z` of `C^q`, read "`z` represents `c(s)`": related sections are cycles whose
class is `c(s)`, every section of `M` locally has a representative, a section whose
representative is a boundary vanishes, and every cycle is locally, up to a boundary, a
representative. Then `c` is an isomorphism (`MMP.DeRham.IsLocalCohomologyRep.isIso`).

This is the form in which the inverse Cartier isomorphism `C⁻¹ : Ω^q(log S) ⟶ ℋ^q(F_*Ω^•(log S))`
is assembled from the affine statement: the relation is "`z` is a closed logarithmic form on an
affine chart representing `C⁻¹ s`", and the four hypotheses are the affine theorem on the charts.

## Main results

* `MMP.DeRham.exists_iCycles_app_eq`: a section of `C^q` killed by the differential is a section
  of the cycles.
* `MMP.DeRham.exists_toCycles_app_eq_of_homologyπ_app_eq_zero`: a cycle whose cohomology class
  vanishes is locally a boundary.
* `MMP.DeRham.IsLocalCohomologyRep`: a relation between sections of `M` and of `C^q` locally
  representing `c : M ⟶ ℋ^q(C)`.
* `MMP.DeRham.IsLocalCohomologyRep.isIso`: **the local criterion for a morphism into a cohomology
  sheaf to be an isomorphism**.

## Implementation notes

Exactness and epimorphisms of sheaves of modules are read on sections through local
surjectivity (`Stacks.SheafOfModules.EpiMono.exists_covering_of_epi` and
`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective`), and
monomorphisms through local injectivity; no stalks are taken. The covering sieves of the site of
open sets are spelled out pointwise (`Opens.mem_grothendieckTopology`).

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §1 and §4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace MMP.DeRham

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

section Cycles

/-- A section of the target of a kernel fork with limit, killed by the morphism, is the image of
a section of the fork point. -/
theorem exists_ι_app_eq_of_isLimit {M N : SheafOfModules.{u} R} {φ : M ⟶ N} {K : KernelFork φ}
    (hK : IsLimit K) (W : Opens X) (z : ToType (M.val.obj (op W)))
    (hz : φ.val.app (op W) z = 0) :
    ∃ w : ToType (K.pt.val.obj (op W)), K.ι.val.app (op W) w = z := by
  let ev := SheafOfModules.evaluation.{u} R (op W)
  have : ev.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_preserves_terminal_object
  let fork : KernelFork (ev.map φ) := K.map ev
  have hfork : IsLimit fork := K.mapIsLimit hK ev
  let g : ModuleCat.of (R.obj.obj (op W)) (R.obj.obj (op W)) ⟶ ev.obj M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ z)
  have hg : g ≫ ev.map φ = 0 := by
    ext
    change φ.val.app (op W) ((1 : R.obj.obj (op W)) • z) = 0
    rw [map_smul, hz, smul_zero]
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hfork g hg
  refine ⟨l (1 : R.obj.obj (op W)), ?_⟩
  have h := congrArg (fun φ : ModuleCat.of (R.obj.obj (op W)) (R.obj.obj (op W)) ⟶
    ev.obj M ↦ φ (1 : R.obj.obj (op W))) hl
  change K.ι.val.app (op W) (l 1) = (1 : R.obj.obj (op W)) • z at h
  rwa [one_smul] at h

variable (C : CochainComplex (SheafOfModules.{u} R) ℕ)

/-- A section of `C^q` killed by the differential `C^q ⟶ C^{q+1}` lifts to a section of the
cycles. -/
theorem exists_iCycles_app_eq (q : ℕ) (W : Opens X) (z : ToType ((C.X q).val.obj (op W)))
    (hz : (C.d q (q + 1)).val.app (op W) z = 0) :
    ∃ z' : ToType ((C.cycles q).val.obj (op W)), (C.iCycles q).val.app (op W) z' = z :=
  exists_ι_app_eq_of_isLimit (C.cyclesIsKernel q (q + 1) (by simp)) W z hz

/-- **A cycle whose cohomology class vanishes is locally a boundary.** -/
theorem exists_toCycles_app_eq_of_homologyπ_app_eq_zero (q : ℕ) (W : Opens X)
    (z : ToType ((C.cycles q).val.obj (op W)))
    (hz : (C.homologyπ q).val.app (op W) z = 0) {x : X} (hx : x ∈ W) :
    ∃ (W' : Opens X) (h : W' ≤ W), x ∈ W' ∧
      ∃ y : ToType ((C.X ((ComplexShape.up ℕ).prev q)).val.obj (op W')),
        (C.toCycles _ q).val.app (op W') y = (C.cycles q).val.map (homOfLE h).op z := by
  let S := ShortComplex.mk (C.toCycles ((ComplexShape.up ℕ).prev q) q) (C.homologyπ q)
    (C.toCycles_comp_homologyπ _ q)
  have hS : S.Exact := S.exact_of_g_is_cokernel (C.homologyIsCokernel _ q rfl)
  have := (S.exact_iff_epi_kernel_lift).1 hS
  obtain ⟨w, hw⟩ := exists_ι_app_eq_of_isLimit (kernelIsKernel S.g) W z hz
  change (kernel.ι S.g).val.app (op W) w = z at hw
  obtain ⟨T, hT, hTw⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
    (kernel.lift S.g S.f S.zero) (V := W) w
  obtain ⟨W', g, hg, hxW'⟩ := (Opens.mem_grothendieckTopology _).1 hT x hx
  obtain ⟨y, hy⟩ := hTw g hg
  refine ⟨W', leOfHom g, hxW', y, ?_⟩
  have hy' := congrArg ((kernel.ι S.g).val.app (op W')) hy
  change (kernel.lift S.g S.f S.zero ≫ kernel.ι S.g).val.app (op W') y =
    (kernel.ι S.g).val.app (op W') ((kernel S.g).val.map g.op w) at hy'
  rwa [kernel.lift_ι, PresheafOfModules.naturality_apply, hw] at hy'

end Cycles

section Criterion

open Stacks.SheafOfModules.ComplexLocality

variable (C : CochainComplex (SheafOfModules.{u} R) ℕ) (q : ℕ) {M : SheafOfModules.{u} R}

/-- A relation `Rep W s z` between sections `s` of `M` and sections `z` of `C^q` over the same
open `W` **locally represents** a morphism `c : M ⟶ ℋ^q(C)` when it is stable under
restriction, related sections `z` are cycles whose class is `c s`, every section of `M` has a
representative locally, a section with a boundary as representative vanishes, and every cycle is
locally a representative up to a boundary. -/
structure IsLocalCohomologyRep (c : M ⟶ C.homology q)
    (Rep : ∀ W : Opens X, ToType (M.val.obj (op W)) → ToType ((C.X q).val.obj (op W)) → Prop) :
    Prop where
  /-- The relation is stable under restriction to smaller opens. -/
  restrict {W W' : Opens X} (h : W' ≤ W) {s z} : Rep W s z →
    Rep W' (M.val.map (homOfLE h).op s) ((C.X q).val.map (homOfLE h).op z)
  /-- A representative is a cycle. -/
  d_eq_zero {W s z} : Rep W s z → (C.d q (q + 1)).val.app (op W) z = 0
  /-- The cohomology class of a representative of `s` is `c s`. -/
  class_eq {W s} {z : ToType ((C.cycles q).val.obj (op W))} :
    Rep W s ((C.iCycles q).val.app (op W) z) →
      c.val.app (op W) s = (C.homologyπ q).val.app (op W) z
  /-- Every section of `M` has a representative locally. -/
  exists_rep (W : Opens X) (s : ToType (M.val.obj (op W))) {x : X} (hx : x ∈ W) :
    ∃ (W' : Opens X) (h : W' ≤ W), x ∈ W' ∧ ∃ z, Rep W' (M.val.map (homOfLE h).op s) z
  /-- A section represented by a boundary vanishes. -/
  eq_zero {W s z} (y : ToType ((C.X ((ComplexShape.up ℕ).prev q)).val.obj (op W))) :
    Rep W s z → (C.d _ q).val.app (op W) y = z → s = 0
  /-- Every cycle is locally a representative up to a boundary. -/
  exists_rep_of_cycle (W : Opens X) (z : ToType ((C.X q).val.obj (op W)))
    (hz : (C.d q (q + 1)).val.app (op W) z = 0) {x : X} (hx : x ∈ W) :
    ∃ (W' : Opens X) (h : W' ≤ W), x ∈ W' ∧ ∃ (s : ToType (M.val.obj (op W')))
      (y : ToType ((C.X ((ComplexShape.up ℕ).prev q)).val.obj (op W')))
      (z' : ToType ((C.X q).val.obj (op W'))), Rep W' s z' ∧
      (C.X q).val.map (homOfLE h).op z = z' + (C.d _ q).val.app (op W') y

variable {C q}

/-- Under a local representation, a section killed by `c` vanishes locally. -/
theorem IsLocalCohomologyRep.locally_eq_zero_of_app_eq_zero {c : M ⟶ C.homology q}
    {Rep : ∀ W : Opens X, ToType (M.val.obj (op W)) → ToType ((C.X q).val.obj (op W)) → Prop}
    (hR : IsLocalCohomologyRep C q c Rep) (W : Opens X) (s : ToType (M.val.obj (op W)))
    (hs : c.val.app (op W) s = 0) {x : X} (hx : x ∈ W) :
    ∃ (W' : Opens X) (h : W' ≤ W), x ∈ W' ∧ M.val.map (homOfLE h).op s = 0 := by
  obtain ⟨W₁, h₁, hx₁, z, hz⟩ := hR.exists_rep W s hx
  obtain ⟨z', rfl⟩ := exists_iCycles_app_eq C q W₁ z (hR.d_eq_zero hz)
  have hπ : (C.homologyπ q).val.app (op W₁) z' = 0 := by
    rw [← hR.class_eq hz, PresheafOfModules.naturality_apply, hs, map_zero]
    rfl
  obtain ⟨W₂, h₂, hx₂, y, hy⟩ :=
    exists_toCycles_app_eq_of_homologyπ_app_eq_zero C q W₁ z' hπ hx₁
  have hd : (C.d _ q).val.app (op W₂) y =
      (C.X q).val.map (homOfLE h₂).op ((C.iCycles q).val.app (op W₁) z') := by
    rw [← PresheafOfModules.naturality_apply, ← hy, comp_val_app_apply, C.toCycles_i]
  refine ⟨W₂, h₂.trans h₁, hx₂, ?_⟩
  rw [show (homOfLE (h₂.trans h₁)).op = (homOfLE h₁).op ≫ (homOfLE h₂).op from rfl,
    PresheafOfModules.map_comp_apply]
  exact hR.eq_zero y (hR.restrict h₂ hz) hd

/-- A locally represented morphism into a cohomology sheaf is a monomorphism. -/
theorem IsLocalCohomologyRep.mono {c : M ⟶ C.homology q}
    {Rep : ∀ W : Opens X, ToType (M.val.obj (op W)) → ToType ((C.X q).val.obj (op W)) → Prop}
    (hR : IsLocalCohomologyRep C q c Rep) : Mono c := by
  have hloc : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf R.obj).map c.val) := by
    refine ⟨fun {W} a b hab ↦ ?_⟩
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    let a' : ToType (M.val.obj (op W.unop)) := a
    let b' : ToType (M.val.obj (op W.unop)) := b
    change c.val.app (op W.unop) a' = c.val.app (op W.unop) b' at hab
    obtain ⟨W', h, hxW', hW'⟩ := hR.locally_eq_zero_of_app_eq_zero W.unop (a' - b')
      (by rw [map_sub, hab, sub_self]) hx
    refine ⟨W', homOfLE h, ?_, hxW'⟩
    change M.val.map (homOfLE h).op a' = M.val.map (homOfLE h).op b'
    rwa [map_sub, sub_eq_zero] at hW'
  have : Sheaf.IsLocallyInjective ((SheafOfModules.toSheaf R).map c) := hloc
  have := Sheaf.mono_of_isLocallyInjective ((SheafOfModules.toSheaf R).map c)
  exact (SheafOfModules.toSheaf R).mono_of_mono_map ‹_›

/-- A locally represented morphism into a cohomology sheaf is an epimorphism. -/
theorem IsLocalCohomologyRep.epi {c : M ⟶ C.homology q}
    {Rep : ∀ W : Opens X, ToType (M.val.obj (op W)) → ToType ((C.X q).val.obj (op W)) → Prop}
    (hR : IsLocalCohomologyRep C q c Rep) : Epi c := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective c ⟨fun {W} h ↦ ?_⟩
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨T, hT, hTh⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
    (C.homologyπ q) (V := W) h
  obtain ⟨W₁, g₁, hg₁, hx₁⟩ := (Opens.mem_grothendieckTopology _).1 hT x hx
  obtain ⟨z₀, hz'⟩ := hTh g₁ hg₁
  let z' : ToType ((C.cycles q).val.obj (op W₁)) := z₀
  change (C.homologyπ q).val.app (op W₁) z' = (C.homology q).val.map g₁.op h at hz'
  have hcyc : (C.d q (q + 1)).val.app (op W₁) ((C.iCycles q).val.app (op W₁) z') = 0 := by
    rw [comp_val_app_apply, C.iCycles_d]
    rfl
  obtain ⟨W₂, h₂, hx₂, s, y, z₂, hrep, hz₂⟩ := hR.exists_rep_of_cycle W₁ _ hcyc hx₁
  let m : ToType ((C.cycles q).val.obj (op W₂)) := (C.cycles q).val.map (homOfLE h₂).op z'
  have key : z₂ = (C.iCycles q).val.app (op W₂) (m - (C.toCycles _ q).val.app (op W₂) y) := by
    rw [map_sub, comp_val_app_apply, C.toCycles_i]
    change z₂ = (C.iCycles q).val.app (op W₂) ((C.cycles q).val.map (homOfLE h₂).op z') - _
    rw [PresheafOfModules.naturality_apply, hz₂, add_sub_cancel_right]
  rw [key] at hrep
  refine ⟨W₂, homOfLE h₂ ≫ g₁, ⟨s, ?_⟩, hx₂⟩
  have hπ0 : (C.homologyπ q).val.app (op W₂) ((C.toCycles _ q).val.app (op W₂) y) = 0 := by
    rw [comp_val_app_apply, C.toCycles_comp_homologyπ]
    rfl
  change c.val.app (op W₂) s = (C.homology q).val.map (homOfLE h₂ ≫ g₁).op h
  rw [hR.class_eq hrep, map_sub, hπ0, sub_zero, PresheafOfModules.naturality_apply, hz',
    op_comp]
  exact (PresheafOfModules.map_comp_apply (C.homology q).val g₁.op (homOfLE h₂).op h).symm

/-- **A morphism into a cohomology sheaf which is locally represented is an isomorphism.** -/
theorem IsLocalCohomologyRep.isIso {c : M ⟶ C.homology q}
    {Rep : ∀ W : Opens X, ToType (M.val.obj (op W)) → ToType ((C.X q).val.obj (op W)) → Prop}
    (hR : IsLocalCohomologyRep C q c Rep) : IsIso c :=
  have := hR.mono
  have := hR.epi
  isIso_of_mono_of_epi c

end Criterion

end MMP.DeRham

end
