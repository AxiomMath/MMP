module

public import MMP.AlgebraicGeometry.DeRham.FrobeniusSplittingGlue

/-!
# The Frobenius map of the logarithmic de Rham complex in degree zero

The sections of `K⁰` are the functions on the complement `U` of the divisor whose restrictions
have no poles; their `p`-th powers have none either (Deligne's criterion in degree `0`), so
`a ↦ a ^ p` is a morphism `c₀ : K⁰ ⟶ F_*K⁰` of sheaves of modules, the Frobenius direct image
carrying the module structure `r • a = r ^ p a`. It represents the inverse Cartier map in degree
`0`.

## Main definitions

* `MMP.DeRham.powZeroForm`: the `p`-th power on `⋀⁰ Ω[L⁄k] = L`.
* `MMP.DeRham.FrobeniusSplittingData.IsSNCChart`: an affine open of `V` with local equations of
  the divisor.
* `MMP.DeRham.FrobeniusSplittingData.frobeniusPow`: `c₀ : K⁰ ⟶ F_*K⁰`, `a ↦ a ^ p`.

## Main results

* `MMP.DeRham.isInvCartierRep_powZeroForm`: `a ^ p` represents `C⁻¹ a`.
* `MMP.DeRham.FrobeniusSplittingData.cartierRep_frobeniusPow`: `c₀` represents the inverse
  Cartier map.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §4.2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius
open KaehlerDifferential KaehlerDifferential.Cartier exteriorPower

universe u v

namespace MMP.DeRham

/-! ### The `p`-th power of functions, read as `0`-forms -/

section RingPow

variable (p : ℕ) [Fact p.Prime] (k : Type u) {L : Type u} [CommRing k] [CommRing L]
  [Algebra k L] [CharP L p]

/-- The `p`-th power map on the `0`-forms `⋀⁰ Ω[L⁄k] = L`. -/
def powZeroForm : ⋀[L]^0 (Ω[L⁄k]) →+ ⋀[L]^0 (Ω[L⁄k]) :=
  (zeroEquiv L (Ω[L⁄k])).symm.toAddMonoidHom.comp
    ((frobenius L p).toAddMonoidHom.comp (zeroEquiv L (Ω[L⁄k])).toAddMonoidHom)

variable {p k}

/-- The `p`-th power of the `0`-form corresponding to `c : L` is the `0`-form of `c ^ p`. -/
@[simp]
theorem powZeroForm_zeroEquiv_symm (c : L) :
    powZeroForm p k ((zeroEquiv L (Ω[L⁄k])).symm c) = (zeroEquiv L (Ω[L⁄k])).symm (c ^ p) := by
  simp [powZeroForm, frobenius_def]

/-- `powZeroForm` is `x ↦ x ^ p` read through `⋀⁰ Ω[L⁄k] ≃ L`. -/
theorem powZeroForm_apply (x : ⋀[L]^0 (Ω[L⁄k])) :
    powZeroForm p k x = (zeroEquiv L (Ω[L⁄k])).symm (zeroEquiv L (Ω[L⁄k]) x ^ p) := by
  simp [powZeroForm, frobenius_def]

/-- The `p`-th power map on `0`-forms is `p`-semilinear: `(c • x) ^ p = c ^ p • x ^ p`. -/
theorem powZeroForm_smul (c : L) (x : ⋀[L]^0 (Ω[L⁄k])) :
    powZeroForm p k (c • x) = c ^ p • powZeroForm p k x := by
  rw [powZeroForm_apply, powZeroForm_apply, map_smul, smul_eq_mul, mul_pow, ← smul_eq_mul,
    map_smul]

/-- `x ↦ x ^ p` represents the inverse Cartier map in degree `0`. -/
theorem isInvCartierRep_powZeroForm (x : ⋀[L]^0 (Ω[L⁄k])) :
    IsInvCartierRep p 0 x (powZeroForm p k x) := by
  obtain ⟨c, rfl⟩ := (zeroEquiv L (Ω[L⁄k])).symm.surjective x
  rw [powZeroForm_zeroEquiv_symm, zeroEquiv_symm_apply, zeroEquiv_symm_apply]
  have h := isInvCartierRep_ιMulti_D (p := p) (A := k) (Fin.elim0 : Fin 0 → L)
  have e1 : ∀ v w : Fin 0 → Ω[L⁄k], ιMulti L 0 v = ιMulti L 0 w := fun v w =>
    congrArg _ (funext fun i => i.elim0)
  rw [e1 (fun i => D k L (Fin.elim0 i)), e1 (fun i => Fin.elim0 i ^ (p - 1) • D k L (Fin.elim0 i))]
    at h
  exact h.smul c

variable {B : Type u} [CommRing B] [Algebra B L] {ι : Type*} {u : ι → B}

/-- The `p`-th power of a logarithmic `0`-form is logarithmic. -/
theorem coe_powZeroForm_mem_logForms (x : ⋀[L]^0 (Ω[L⁄k]))
    (hx : (x : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 0) :
    ((powZeroForm p k x : ⋀[L]^0 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈ logForms k L u 0 := by
  let S : Submodule B (⋀[L]^0 (Ω[L⁄k])) :=
    { carrier := {x | ((powZeroForm p k x : ⋀[L]^0 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
        logForms k L u 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        simpa only [Set.mem_ofPred_eq, map_add, Submodule.coe_add] using add_mem hx hy
      smul_mem' := by
        intro b x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [← algebraMap_smul L b x, powZeroForm_smul, ← map_pow, algebraMap_smul,
          Submodule.coe_smul_of_tower]
        exact Submodule.smul_mem _ _ hx }
  refine mem_of_mem_logForms S (fun v _ => ?_) x hx
  change ((powZeroForm p k (ιMulti L 0 v) : ⋀[L]^0 (Ω[L⁄k])) : ExteriorAlgebra L (Ω[L⁄k])) ∈
    logForms k L u 0
  rw [powZeroForm_apply, zeroEquiv_ιMulti, one_pow, ← zeroEquiv_ιMulti (R := L) v,
    LinearEquiv.symm_apply_apply, ιMulti_apply_coe]
  exact ιMulti_mem_logForms _ fun m => m.elim0

/-- Base change of `0`-forms along `L → L'` commutes with the `p`-th power map. -/
theorem mapExteriorPower_powZeroForm {L' : Type u} [CommRing L'] [Algebra k L'] [Algebra L L']
    [IsScalarTower k L L'] [CharP L' p] (x : ⋀[L]^0 (Ω[L⁄k])) :
    mapExteriorPower k L L' 0 (powZeroForm p k x) =
      powZeroForm p k (mapExteriorPower k L L' 0 x) := by
  obtain ⟨c, rfl⟩ := (zeroEquiv L (Ω[L⁄k])).symm.surjective x
  rw [powZeroForm_zeroEquiv_symm, mapExteriorPower_zeroEquiv_symm,
    mapExteriorPower_zeroEquiv_symm, powZeroForm_zeroEquiv_symm, map_pow]

end RingPow

namespace FrobeniusSplittingData

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{u}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type v} [Fintype ι] [HasDerivedCategory.{u} V.Modules]
  (D : FrobeniusSplittingData p k n f ι)

/-! ### Charts of the divisor on `V` -/

/-- An affine open of `V` on which every component of the divisor has a local equation. -/
def IsSNCChart (W : V.affineOpens) : Prop :=
  ∃ t : ι → Γ(V, W), ∀ j, (D.J j).ideal W = Ideal.span {t j}

variable {D}

/-- For a chart `W` of the divisor, `W ⊓ U` is affine. -/
theorem IsSNCChart.isAffineOpen_inf {W : V.affineOpens} (h : D.IsSNCChart W) :
    IsAffineOpen ((W : V.Opens) ⊓ D.U) := by
  rw [inf_eq_basicOpen_prod_of_ideal_eq_span D.J D.U D.hU W _ h.choose_spec]
  exact W.2.basicOpen _

/-- The affine open `W ⊓ U` of a chart of the divisor. -/
abbrev IsSNCChart.affineInf {W : V.affineOpens} (h : D.IsSNCChart W) : V.affineOpens :=
  ⟨_, h.isAffineOpen_inf⟩

/-- A basic open of a chart of the divisor is a chart of the divisor. -/
theorem IsSNCChart.basicOpen {W : V.affineOpens} (h : D.IsSNCChart W) (b : Γ(V, W)) :
    D.IsSNCChart ⟨V.basicOpen b, W.2.basicOpen b⟩ := by
  obtain ⟨t, ht⟩ := h
  refine ⟨fun j => V.presheaf.map (homOfLE (V.basicOpen_le b)).op (t j), fun j => ?_⟩
  have := (D.J j).map_ideal (U := ⟨V.basicOpen b, W.2.basicOpen b⟩) (V := W) (V.basicOpen_le b)
  rw [← this, ht, Ideal.map_span, Set.image_singleton]
  rfl

variable (D)

/-- Every point of an open `W` of `V` lies in a chart of the divisor contained in `W`. -/
theorem exists_isSNCChart {W : V.Opens} {x : V} (hx : x ∈ W) :
    ∃ a : {W : V.affineOpens // D.IsSNCChart W}, x ∈ (a.1 : V.Opens) ∧ (a.1 : V.Opens) ≤ W := by
  obtain ⟨W₀, t₀, hxW₀, hideal, -⟩ := exists_affineOpen_snc_chart f D.J D.hJ D.U D.hU x
  obtain ⟨b, hb, hxb⟩ := W₀.2.exists_basicOpen_le (V := W) ⟨x, hx⟩ hxW₀
  exact ⟨⟨⟨V.basicOpen b, W₀.2.basicOpen b⟩, IsSNCChart.basicOpen ⟨t₀, hideal⟩ b⟩, hxb, hb⟩

/-! ### The `p`-th power on the sections of `K⁰` -/

variable {D}

open scoped Classical in
/-- The `p`-th power of functions on `W ⊓ U`, read on the sections of `Ω⁰` (zero when
`W ⊓ U` is empty). -/
def powForm {W : V.affineOpens} (h : D.IsSNCChart W) :
    Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), h.affineInf) →+
      Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), h.affineInf) :=
  letI := MMP.Mori.sectionAlgebra f h.affineInf
  if hL : Nontrivial Γ(V, h.affineInf) then
    haveI := charP_of_nontrivial D h.affineInf
    (formsAlgEquiv f 0 h.affineInf).symm.toAddMonoidHom.comp
      ((powZeroForm p k).comp (formsAlgEquiv f 0 h.affineInf).toAddMonoidHom)
  else 0

/-- When `W ⊓ U` has nonzero functions, `powForm` is `powZeroForm` read through
`formsAlgEquiv`. -/
theorem formsAlgEquiv_powForm {W : V.affineOpens} (h : D.IsSNCChart W)
    [hL : Nontrivial Γ(V, h.affineInf)]
    (ω : Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), h.affineInf)) :
    letI := MMP.Mori.sectionAlgebra f h.affineInf
    haveI := charP_of_nontrivial D h.affineInf
    formsAlgEquiv f 0 h.affineInf (powForm h ω) =
      powZeroForm p k (formsAlgEquiv f 0 h.affineInf ω) := by
  classical
  rw [powForm, dite_eq_left hL]
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- `powForm` is `p`-semilinear over the functions on `W ⊓ U`. -/
theorem powForm_smul {W : V.affineOpens} (h : D.IsSNCChart W) (c : Γ(V, h.affineInf))
    (ω : Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), h.affineInf)) :
    powForm h (c • ω) = c ^ p • powForm h ω := by
  classical
  by_cases hL : Nontrivial Γ(V, h.affineInf)
  · let := MMP.Mori.sectionAlgebra f h.affineInf
    have := charP_of_nontrivial D h.affineInf
    rw [powForm, dite_eq_left hL]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      LinearEquiv.map_smul, powZeroForm_smul]
  · have : Subsingleton Γ(V, h.affineInf) := not_nontrivial_iff_subsingleton.1 hL
    have := Module.subsingleton Γ(V, h.affineInf)
      Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), h.affineInf)
    exact Subsingleton.elim _ _

/-- The `p`-th power of the restriction of a section of `K⁰` to `W ⊓ U` is again the restriction
of a section of `K⁰`. -/
theorem powForm_mem_range {W : V.affineOpens} (h : D.IsSNCChart W) (s : Γ(D.K 0, W)) :
    powForm h (D.e 0 _ s) ∈ Set.range (D.e 0 W) := by
  classical
  by_cases hL : Nontrivial Γ(V, h.affineInf)
  swap
  · rw [powForm, dite_eq_right hL]
    exact ⟨0, map_zero _⟩
  have hcrit := D.mem_range_e_iff W h.choose h.choose_spec 0
  have hs := (hcrit (D.e 0 _ s)).1 ⟨s, rfl⟩
  let := MMP.Mori.sectionAlgebra f h.affineInf
  let : Algebra Γ(V, W) Γ(V, h.affineInf) :=
    (V.presheaf.map (homOfLE (inf_le_left : (W : V.Opens) ⊓ D.U ≤ W)).op).hom.toAlgebra
  have := charP_of_nontrivial D h.affineInf
  have key : ((formsAlgEquiv f 0 h.affineInf (powForm h (D.e 0 _ s)) :
      ⋀[Γ(V, h.affineInf)]^0 (Ω[Γ(V, h.affineInf)⁄k])) :
        ExteriorAlgebra Γ(V, h.affineInf) (Ω[Γ(V, h.affineInf)⁄k])) ∈
      logForms k Γ(V, h.affineInf) h.choose 0 := by
    rw [formsAlgEquiv_powForm]
    have := coe_powZeroForm_mem_logForms (p := p) (u := h.choose)
      (formsAlgEquiv f 0 h.affineInf (D.e 0 _ s)) (by convert hs using 3)
    convert this using 3
  exact (hcrit _).2 (by convert key using 3)

/-- `powForm` commutes with restriction between charts. -/
theorem powForm_map {W W' : V.affineOpens} (h : D.IsSNCChart W) (h' : D.IsSNCChart W')
    (hA : (h'.affineInf : V.Opens) ≤ h.affineInf)
    (ω : Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), h.affineInf)) :
    powForm h' ((f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hA).op ω) =
      (f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hA).op (powForm h ω) := by
  by_cases hL' : Nontrivial Γ(V, h'.affineInf)
  swap
  · have : Subsingleton Γ(V, h'.affineInf) := not_nontrivial_iff_subsingleton.1 hL'
    have := Module.subsingleton Γ(V, h'.affineInf)
      Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), h'.affineInf)
    exact Subsingleton.elim _ _
  have : Nontrivial Γ(V, h.affineInf) := nontrivial_of_le D hA
  have := charP_of_nontrivial D h.affineInf
  have := charP_of_nontrivial D h'.affineInf
  let := MMP.Mori.sectionAlgebra f h.affineInf
  let := MMP.Mori.sectionAlgebra f h'.affineInf
  let : Algebra Γ(V, h.affineInf) Γ(V, h'.affineInf) :=
    (V.presheaf.map (homOfLE hA).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hA
  refine (formsAlgEquiv f 0 h'.affineInf).injective ?_
  have r2 := formsAlgEquiv_restrict f 0 (W := h.affineInf) (W' := h'.affineInf) hA (powForm h ω)
  have p2 := formsAlgEquiv_powForm h ω
  have m := mapExteriorPower_powZeroForm (p := p) (k := k) (L' := Γ(V, h'.affineInf))
    (formsAlgEquiv f 0 h.affineInf ω)
  rw [formsAlgEquiv_powForm, formsAlgEquiv_restrict f 0 hA]
  refine Eq.trans ?_ r2.symm
  rw [p2]
  exact m.symm

/-- The `p`-th power on the sections of `K⁰` over a chart. -/
def powPiece {W : V.affineOpens} (h : D.IsSNCChart W) : Γ(D.K 0, W) →+ Γ(D.K 0, W) :=
  AddMonoidHom.mk' (fun s => (powForm_mem_range h s).choose) fun s s' => D.he_inj 0 _ (by
    rw [(powForm_mem_range h _).choose_spec, map_add, map_add, map_add,
      (powForm_mem_range h s).choose_spec, (powForm_mem_range h s').choose_spec])

/-- The restriction of `powPiece h s` to `W ⊓ U` is the `p`-th power of that of `s`. -/
theorem e_powPiece {W : V.affineOpens} (h : D.IsSNCChart W) (s : Γ(D.K 0, W)) :
    D.e 0 _ (powPiece h s) = powForm h (D.e 0 _ s) :=
  (powForm_mem_range h s).choose_spec

/-- `powPiece` is `p`-semilinear over the functions on `W`. -/
theorem powPiece_smul {W : V.affineOpens} (h : D.IsSNCChart W) (r : Γ(V, W))
    (s : Γ(D.K 0, W)) : powPiece h (r • s) = r ^ p • powPiece h s := by
  refine D.he_inj 0 _ ?_
  rw [e_powPiece, D.he_smul, D.he_smul, e_powPiece, powForm_smul, map_pow]

/-- `powPiece` commutes with restriction between charts. -/
theorem powPiece_map {W W' : V.affineOpens} (h : D.IsSNCChart W) (h' : D.IsSNCChart W')
    (hle : (W' : V.Opens) ≤ W) (s : Γ(D.K 0, W)) :
    powPiece h' ((D.K 0).presheaf.map (homOfLE hle).op s) =
      (D.K 0).presheaf.map (homOfLE hle).op (powPiece h s) := by
  refine D.he_inj 0 _ ?_
  rw [e_powPiece, D.he_res, D.he_res, e_powPiece]
  exact powForm_map h h' (inf_le_inf_right D.U hle) _

/-- The `p`-th power represents the inverse Cartier map on every affine open of a chart. -/
theorem isInvCartierRep_powForm {W : V.affineOpens} (h : D.IsSNCChart W) (G : V.affineOpens)
    (hG : (G : V.Opens) ≤ h.affineInf) [CharP Γ(V, G) p]
    (ω : Γ(f.relativeDifferentialForms ((0 : ℕ) : ℤ), h.affineInf)) :
    letI := MMP.Mori.sectionAlgebra f G
    IsInvCartierRep p 0
      (formsAlgEquiv f 0 G ((f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map
        (homOfLE hG).op ω))
      (formsAlgEquiv f 0 G ((f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map
        (homOfLE hG).op (powForm h ω))) := by
  have : Nontrivial Γ(V, G) := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  have : Nontrivial Γ(V, h.affineInf) := nontrivial_of_le D hG
  have := charP_of_nontrivial D h.affineInf
  let := MMP.Mori.sectionAlgebra f h.affineInf
  let := MMP.Mori.sectionAlgebra f G
  let : Algebra Γ(V, h.affineInf) Γ(V, G) := (V.presheaf.map (homOfLE hG).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hG
  have r1 := formsAlgEquiv_restrict f 0 (W := h.affineInf) (W' := G) hG ω
  have r2 := formsAlgEquiv_restrict f 0 (W := h.affineInf) (W' := G) hG (powForm h ω)
  have p2 := formsAlgEquiv_powForm h ω
  have m := mapExteriorPower_powZeroForm (p := p) (k := k) (L' := Γ(V, G))
    (formsAlgEquiv f 0 h.affineInf ω)
  rw [r1, r2, p2, m]
  exact isInvCartierRep_powZeroForm _

/-! ### The morphism `K⁰ ⟶ F_*K⁰` -/

variable (D)

/-- The charts of the divisor form a basis of the topology of `V`. -/
theorem isSNCChart_basis : ∀ W ≤ (⊤ : V.Opens), ∀ x ∈ W,
    ∃ a : {W : V.affineOpens // D.IsSNCChart W}, x ∈ (a.1 : V.Opens) ∧ (a.1 : V.Opens) ≤ W :=
  fun _ _ _ hx => D.exists_isSNCChart hx

/-- The `p`-th power on the sections of `K⁰` over any open. -/
def powSection (W : V.Opens) : Γ(D.K 0, W) →+ Γ(D.K 0, W) :=
  glue (fun a : {W : V.affineOpens // D.IsSNCChart W} => (a.1 : V.Opens)) D.isSNCChart_basis
    (fun _ => le_top) (fun a => powPiece a.2) (fun a b => powPiece_map a.2 b.2) (le_top : W ≤ ⊤)

/-- The restriction of `powSection W s` to a chart `W' ≤ W` is `powPiece` of the restriction of
`s`. -/
theorem powSection_spec (W : V.Opens) (s : Γ(D.K 0, W)) {W' : V.affineOpens}
    (h : D.IsSNCChart W') (hW' : (W' : V.Opens) ≤ W) :
    (D.K 0).presheaf.map (homOfLE hW').op (D.powSection W s) =
      powPiece h ((D.K 0).presheaf.map (homOfLE hW').op s) :=
  glue_spec (fun a : {W : V.affineOpens // D.IsSNCChart W} => (a.1 : V.Opens)) D.isSNCChart_basis
    (fun _ => le_top) (fun a => powPiece a.2) (fun a b => powPiece_map a.2 b.2)
    (le_top : W ≤ ⊤) s ⟨W', h⟩ hW'

/-- `powSection` is `p`-semilinear over the functions on `W`. -/
theorem powSection_smul (W : V.Opens) (r : Γ(V, W)) (s : Γ(D.K 0, W)) :
    D.powSection W (r • s) = r ^ p • D.powSection W s :=
  glue_smul (fun a : {W : V.affineOpens // D.IsSNCChart W} => (a.1 : V.Opens)) D.isSNCChart_basis
    (fun _ => le_top) (fun a => powPiece a.2) (fun a b => powPiece_map a.2 b.2) p
    (fun a r s => powPiece_smul a.2 r s) (le_top : W ≤ ⊤) r s

/-- `powSection` commutes with restriction. -/
theorem powSection_map {W₁ W₂ : V.Opens} (h : W₁ ≤ W₂) (s : Γ(D.K 0, W₂)) :
    D.powSection W₁ ((D.K 0).presheaf.map (homOfLE h).op s) =
      (D.K 0).presheaf.map (homOfLE h).op (D.powSection W₂ s) :=
  glue_res (fun a : {W : V.affineOpens // D.IsSNCChart W} => (a.1 : V.Opens)) D.isSNCChart_basis
    (fun _ => le_top) (fun a => powPiece a.2) (fun a b => powPiece_map a.2 b.2)
    le_top le_top h s

/-- **The Frobenius map `c₀ : K⁰ ⟶ F_*K⁰`, `a ↦ a ^ p`**. -/
def frobeniusPow :
    D.K 0 ⟶ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K 0) :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (D.powSection W.unop)
      naturality := fun W₁ W₂ g => by
        ext s
        change D.powSection W₂.unop ((D.K 0).presheaf.map (homOfLE (leOfHom g.unop)).op s) =
          (D.K 0).presheaf.map (homOfLE (leOfHom g.unop)).op (D.powSection W₁.unop s)
        exact D.powSection_map (leOfHom g.unop) s }
    fun (W : (V.Opens)ᵒᵖ) (r : Γ(V, W.unop)) (s : Γ(D.K 0, W.unop)) => by
      change D.powSection W.unop (r • s) = _
      rw [D.powSection_smul]
      exact (D.pushforward_smul (D.K 0) W.unop r _).symm⟩

/-- On the sections over `W`, `frobeniusPow` is `powSection W`. -/
theorem frobeniusPow_app (W : V.Opens) (s : Γ(D.K 0, W)) :
    D.frobeniusPow.app W s = D.powSection W s := rfl

/-- **`c₀` represents the inverse Cartier map in degree `0`**. -/
theorem cartierRep_frobeniusPow (W : V.Opens) (s : Γ(D.K 0, W)) :
    D.cartierRep 0 W s (D.frobeniusPow.app W s) := by
  rw [frobeniusPow_app]
  intro W'' hW'' _
  refine D.isInvCartierRep_of_forall_mem 0 W'' _ _ fun y hy => ?_
  obtain ⟨a, hya, haW⟩ := D.exists_isSNCChart (hW'' hy).1
  have hyP : y ∈ (a.2.affineInf : V.Opens) := ⟨hya, (hW'' hy).2⟩
  obtain ⟨g, g', hgg', hyg⟩ := exists_basicOpen_le_affine_inter W''.2 a.2.isAffineOpen_inf y
    ⟨hy, hyP⟩
  obtain ⟨G, hGg⟩ : ∃ G : V.affineOpens, (G : V.Opens) = V.basicOpen g :=
    ⟨⟨_, W''.2.basicOpen g⟩, rfl⟩
  have hGP : (G : V.Opens) ≤ (a.2.affineInf : V.Opens) := hGg ▸ hgg' ▸ V.basicOpen_le g'
  have hG : (G : V.Opens) ≤ W'' := hGg ▸ V.basicOpen_le g
  refine ⟨G, hG, g, hGg, hGg ▸ hyg, ?_⟩
  intro _
  have key := isInvCartierRep_powForm a.2 G hGP
    (D.e 0 (a.1 : V.Opens) ((D.K 0).presheaf.map (homOfLE haW).op s))
  have hk : (G : V.Opens) ≤ W ⊓ D.U := hG.trans hW''
  have e1 : (f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hGP).op
      (D.e 0 (a.1 : V.Opens) ((D.K 0).presheaf.map (homOfLE haW).op s)) =
      (f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hG).op
        ((f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hW'').op
          (D.e 0 W s)) := by
    rw [D.he_res, presheaf_map_map _ _ (homOfLE hk), presheaf_map_map _ _ (homOfLE hk)]
  have e2 : (f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hGP).op
      (powForm a.2 (D.e 0 (a.1 : V.Opens) ((D.K 0).presheaf.map (homOfLE haW).op s))) =
      (f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hG).op
        ((f.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hW'').op
          (D.e 0 W (D.powSection W s))) := by
    rw [← e_powPiece, ← D.powSection_spec W s a.2 haW, D.he_res, presheaf_map_map _ _ (homOfLE hk),
      presheaf_map_map _ _ (homOfLE hk)]
  rw [e1, e2] at key
  exact key

end FrobeniusSplittingData

end MMP.DeRham
