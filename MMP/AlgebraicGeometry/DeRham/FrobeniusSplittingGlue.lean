module

public import MMP.AlgebraicGeometry.DeRham.FrobeniusSplittingCharts

/-!
# Gluing the local Frobenius splittings

Maps between sheaves of modules given on the members of a basis of opens inside an open `A`,
compatible with restriction, extend uniquely to all opens inside `A`
(`MMP.DeRham.glue`). Applied to the pieces of a chart with a Frobenius lift
(`MMP.DeRham.FrobeniusSplittingData.FrobeniusLiftChart`), this gives the Frobenius splitting
`φ` of a chart on all opens inside it, and for two charts the homotopy `η` between their
splittings. The splittings represent the inverse Cartier map: the inverse Cartier relation on an
affine open is local (`MMP.DeRham.FrobeniusSplittingData.isInvCartierRep_of_forall_mem`). A cover
of `V` by such charts therefore gives local Frobenius splittings of the logarithmic de Rham
complex.

## Main definitions

* `MMP.DeRham.glue`: the extension of local maps from a basis.
* `MMP.DeRham.FrobeniusSplittingData.FrobeniusLiftChart.phi`: the splitting of a chart.
* `MMP.DeRham.FrobeniusSplittingData.homotopy`: the homotopy between the splittings of two
  charts.
* `MMP.DeRham.FrobeniusSplittingData.localFrobeniusSplittingOfCharts`: the local Frobenius
  splittings of a cover by charts.

## Main results

* `MMP.DeRham.IsInvCartierRep.of_forall_isMaximal`: the inverse Cartier relation is local on the
  spectrum.
* `MMP.DeRham.FrobeniusSplittingData.cartierRep_phi`: the splitting of a chart represents the
  inverse Cartier map.
* `MMP.DeRham.FrobeniusSplittingData.nonempty_localFrobeniusSplitting_of_forall_exists_chart`:
  charts through every point give local Frobenius splittings.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §2 and §4.2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius
open KaehlerDifferential KaehlerDifferential.Cartier

universe u v

namespace MMP.DeRham

/-! ### Extending local maps of sheaves from a basis -/

section Glue

variable {X : Scheme.{u}} {M N : X.Modules} {κ : Type*} (O : κ → X.Opens) {A : X.Opens}
  (hbasis : ∀ W ≤ A, ∀ x ∈ W, ∃ a, x ∈ O a ∧ O a ≤ W)

include hbasis in
/-- Sections over an open `W ⊆ A` agreeing on the members of a basis inside `W` agree. -/
theorem eq_of_forall_basis {W : X.Opens} (hW : W ≤ A) {s t : Γ(N, W)}
    (h : ∀ a (ha : O a ≤ W), N.presheaf.map (homOfLE ha).op s = N.presheaf.map (homOfLE ha).op t) :
    s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun a : {a // O a ≤ W} => O a.1) W (fun a => homOfLE a.2) ?_ s t (fun a => h a.1 a.2)
  intro x hx
  obtain ⟨a, hxa, ha⟩ := hbasis W hW x hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

variable (hOA : ∀ a, O a ≤ A) (ψ : ∀ a, Γ(M, O a) →+ Γ(N, O a))
  (hψ : ∀ a b (h : O b ≤ O a) (s : Γ(M, O a)),
    ψ b (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (ψ a s))

include hbasis hOA hψ in
/-- For a section `s` over an open `W ⊆ A` there is a section over `W` whose restriction to every
member `O a ⊆ W` of the basis is `ψ a` of the restriction of `s`. -/
theorem exists_glue {W : X.Opens} (hW : W ≤ A) (s : Γ(M, W)) :
    ∃ t : Γ(N, W), ∀ a (ha : O a ≤ W),
      N.presheaf.map (homOfLE ha).op t = ψ a (M.presheaf.map (homOfLE ha).op s) := by
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X) (fun a : {a // O a ≤ W} => O a.1) W
    (fun a => homOfLE a.2) (fun x hx => by
      obtain ⟨a, hxa, ha⟩ := hbasis W hW x hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩)
    (fun a => ψ a.1 (M.presheaf.map (homOfLE a.2).op s)) (fun a b => by
      refine eq_of_forall_basis O hbasis ((inf_le_left.trans (hOA a.1))) fun c hc => ?_
      change N.presheaf.map _ (N.presheaf.map _ _) = N.presheaf.map _ (N.presheaf.map _ _)
      rw [presheaf_map_map _ _ (homOfLE (hc.trans inf_le_left)),
        presheaf_map_map _ _ (homOfLE (hc.trans inf_le_right)), ← hψ, ← hψ,
        presheaf_map_map _ _ (homOfLE (hc.trans (inf_le_left.trans a.2))),
        presheaf_map_map _ _ (homOfLE (hc.trans (inf_le_left.trans a.2)))])
  exact ⟨t, fun a ha => ht ⟨a, ha⟩⟩

/-- **The extension of local maps from a basis**: the map on sections over `W ⊆ A` whose
restriction to every member `O a ⊆ W` of the basis is `ψ a`. -/
def glue {W : X.Opens} (hW : W ≤ A) : Γ(M, W) →+ Γ(N, W) :=
  AddMonoidHom.mk' (fun s => (exists_glue O hbasis hOA ψ hψ hW s).choose) fun s s' =>
    eq_of_forall_basis O hbasis hW fun a ha => by
      rw [(exists_glue O hbasis hOA ψ hψ hW _).choose_spec a ha, map_add, map_add, map_add,
        (exists_glue O hbasis hOA ψ hψ hW s).choose_spec a ha,
        (exists_glue O hbasis hOA ψ hψ hW s').choose_spec a ha]

/-- The restriction of `glue` to a member `O a ⊆ W` of the basis is `ψ a` of the restriction. -/
theorem glue_spec {W : X.Opens} (hW : W ≤ A) (s : Γ(M, W)) (a : κ) (ha : O a ≤ W) :
    N.presheaf.map (homOfLE ha).op (glue O hbasis hOA ψ hψ hW s) =
      ψ a (M.presheaf.map (homOfLE ha).op s) :=
  (exists_glue O hbasis hOA ψ hψ hW s).choose_spec a ha

/-- `glue` commutes with restriction along `W₁ ⊆ W₂ ⊆ A`. -/
theorem glue_res {W₁ W₂ : X.Opens} (h₁ : W₁ ≤ A) (h₂ : W₂ ≤ A) (h : W₁ ≤ W₂) (s : Γ(M, W₂)) :
    glue O hbasis hOA ψ hψ h₁ (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (glue O hbasis hOA ψ hψ h₂ s) :=
  eq_of_forall_basis O hbasis h₁ fun a ha => by
    rw [glue_spec, presheaf_map_map _ _ (homOfLE (ha.trans h)),
      presheaf_map_map _ _ (homOfLE (ha.trans h)), glue_spec]

/-- If every `ψ a` is `p`-semilinear, `ψ a (r • s) = r ^ p • ψ a s`, then so is `glue`. -/
theorem glue_smul (p : ℕ) (hsmul : ∀ a (r : Γ(X, O a)) (s : Γ(M, O a)), ψ a (r • s) = r ^ p • ψ a s)
    {W : X.Opens} (hW : W ≤ A) (r : Γ(X, W)) (s : Γ(M, W)) :
    glue O hbasis hOA ψ hψ hW (r • s) = r ^ p • glue O hbasis hOA ψ hψ hW s :=
  eq_of_forall_basis O hbasis hW fun a ha => by
    rw [glue_spec, Scheme.Modules.map_smul, hsmul, Scheme.Modules.map_smul, glue_spec, map_pow]

end Glue

/-! ### Inverse Cartier representatives are local -/

section Descent

variable {p : ℕ} [Fact p.Prime] {A L : Type u} [CommRing A] [CommRing L] [Algebra A L]
  [CharP L p]

/-- **The inverse Cartier relation is local**: `x` represents `C⁻¹ ω` as soon as, near every
maximal ideal, `x` differs from a representative `x₀` by an exact form up to a `p`-th power. -/
theorem IsInvCartierRep.of_forall_isMaximal {i : ℕ} {ω x x₀ : ⋀[L]^i (Ω[L⁄A])}
    (h₀ : IsInvCartierRep p i ω x₀)
    (hloc : ∀ 𝔪 : Ideal L, 𝔪.IsMaximal → ∃ g ∉ 𝔪,
      twist p (g ^ p • (x - x₀)) ∈ exactForms p A L i) :
    IsInvCartierRep p i ω x := by
  have hp := (Fact.out : p.Prime)
  have h1 := of_forall_exists_notMem
    (Q := fun b : L => twist p (b ^ p • (x - x₀)) ∈ exactForms p A L i)
    (by simp only [zero_pow hp.ne_zero, zero_smul, map_zero]; exact zero_mem _)
    (fun a b ha hb => by
      simp only [add_pow_char, add_smul, map_add] at ha hb ⊢
      exact add_mem ha hb)
    (fun c b hb => by
      simp only [mul_pow, mul_smul] at hb ⊢
      rw [← smul_twist]
      exact Submodule.smul_mem _ _ hb) hloc
  simp only [one_pow, one_smul] at h1
  exact h₀.of_sub_mem_exactForms h1

end Descent

namespace FrobeniusSplittingData

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{u}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type v} [Fintype ι] [HasDerivedCategory.{u} V.Modules]
  (D : FrobeniusSplittingData p k n f ι)

/-! ### Inverse Cartier representatives on affine opens are local -/

include D in
/-- **The inverse Cartier relation on an affine open is local**: it holds for the forms of `s`
and `z` on an affine open `W''` as soon as every point of `W''` has a basic open
neighbourhood `G` on which it holds. -/
theorem isInvCartierRep_of_forall_mem (q : ℕ) (W'' : V.affineOpens) [CharP Γ(V, W'') p]
    (s z : Γ(f.relativeDifferentialForms (q : ℤ), W''))
    (hloc : ∀ y ∈ (W'' : V.Opens), ∃ (G : V.affineOpens) (hG : (G : V.Opens) ≤ W'')
      (g : Γ(V, W'')), (G : V.Opens) = V.basicOpen g ∧ y ∈ (G : V.Opens) ∧
      ∀ [CharP Γ(V, G) p],
        letI := MMP.Mori.sectionAlgebra f G
        IsInvCartierRep p q
          (formsAlgEquiv f q G ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
            (homOfLE hG).op s))
          (formsAlgEquiv f q G ((f.relativeDifferentialForms (q : ℤ)).presheaf.map
            (homOfLE hG).op z))) :
    letI := MMP.Mori.sectionAlgebra f W''
    IsInvCartierRep p q (formsAlgEquiv f q W'' s) (formsAlgEquiv f q W'' z) := by
  let := MMP.Mori.sectionAlgebra f W''
  obtain ⟨x₀, h₀⟩ := exists_isInvCartierRep (p := p) q (formsAlgEquiv f q W'' s)
  refine h₀.of_forall_isMaximal fun 𝔪 h𝔪 => ?_
  have hy : W''.2.fromSpec ⟨𝔪, h𝔪.isPrime⟩ ∈ (W'' : V.Opens) :=
    (Set.ext_iff.1 W''.2.range_fromSpec _).1 ⟨_, rfl⟩
  obtain ⟨G, hG, g, hGg, hyG, hrepG⟩ := hloc _ hy
  have hg𝔪 : g ∉ 𝔪 := by
    have hmem : (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum Γ(V, W'')) ∈
        W''.2.fromSpec ⁻¹ᵁ V.basicOpen g := hGg ▸ hyG
    rw [W''.2.fromSpec_preimage_basicOpen] at hmem
    exact hmem
  have : Nontrivial Γ(V, G) := (V.presheaf.germ (G : V.Opens) _ hyG).hom.domain_nontrivial
  have := charP_of_nontrivial D G
  let := MMP.Mori.sectionAlgebra f G
  let : Algebra Γ(V, W'') Γ(V, G) := (V.presheaf.map (homOfLE hG).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hG
  have : IsLocalization.Away (algebraMap Γ(V, W'') Γ(V, W'') g) Γ(V, G) := by
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    exact W''.2.isLocalization_of_eq_basicOpen g (homOfLE hG) hGg
  have hrep := hrepG
  rw [formsAlgEquiv_restrict f q hG, formsAlgEquiv_restrict f q hG] at hrep
  have hex := (h₀.map (L' := Γ(V, G))).sub_mem_exactForms hrep
  rw [← map_sub] at hex
  obtain ⟨K, hK⟩ := exists_pow_smul_mem_exactForms (B := Γ(V, W'')) (L' := Γ(V, G)) g _ hex
  refine ⟨g ^ K, fun h => hg𝔪 (h𝔪.isPrime.mem_of_pow_mem K h), ?_⟩
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using hK

namespace FrobeniusLiftChart

variable {D} (C : D.FrobeniusLiftChart)

/-- The local Frobenius form represents the inverse Cartier image, on every affine open of the
piece. -/
theorem isInvCartierRep_frobeniusForm {Õ : D.𝒱.Opens} (h : C.IsBasic Õ) (G : V.affineOpens)
    (hG : (G : V.Opens) ≤ D.pieceAffine Õ h.isAffineOpen_inf_U) [CharP Γ(V, G) p]
    (ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), D.pieceAffine Õ h.isAffineOpen_inf_U)) :
    letI := MMP.Mori.sectionAlgebra f G
    IsInvCartierRep p 1
      (formsAlgEquiv f 1 G ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE hG).op ω))
      (formsAlgEquiv f 1 G ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE hG).op (C.frobeniusForm h ω))) := by
  have : Nontrivial Γ(V, G) := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  have : Nontrivial Γ(V, D.pieceAffine Õ h.isAffineOpen_inf_U) := nontrivial_of_le D hG
  have := charP_of_nontrivial D (D.pieceAffine Õ h.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f (D.pieceAffine Õ h.isAffineOpen_inf_U)
  let := MMP.Mori.sectionAlgebra f G
  let : Algebra Γ(V, D.pieceAffine Õ h.isAffineOpen_inf_U) Γ(V, G) :=
    (V.presheaf.map (homOfLE hG).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res f hG
  rw [formsAlgEquiv_restrict f 1 hG, formsAlgEquiv_restrict f 1 hG,
    C.formsAlgEquiv_frobeniusForm h]
  have := (isInvCartierRep_frobeniusLiftForm k
    (D.isReductionModP_pieceReductionAt Õ h.isAffineOpen_inf_U h.inf_U.isAffineOpen)
    (C.isFrobeniusLift_liftOn h.inf_U)
    (formsAlgEquiv f 1 (D.pieceAffine Õ h.isAffineOpen_inf_U) ω)).map (L' := Γ(V, G))
  convert this using 1

end FrobeniusLiftChart

/-! ### Bases of opens basic in several charts -/

/-- A point `y` of an affine open `Õ` of the lifting that lies in the open `C.𝒲` of a chart has a
basic open neighbourhood `D(b) ⊆ Õ` that is a basic open of `C`. -/
theorem exists_isBasic_basicOpen {Õ : D.𝒱.Opens} (hÕ : IsAffineOpen Õ)
    (C : D.FrobeniusLiftChart) {y : D.𝒱} (hy : y ∈ Õ) (hyC : y ∈ C.𝒲) :
    ∃ b : Γ(D.𝒱, Õ), y ∈ D.𝒱.basicOpen b ∧ C.IsBasic (D.𝒱.basicOpen b) := by
  obtain ⟨b, g, hbg, hyb⟩ := exists_basicOpen_le_affine_inter hÕ C.isAffineOpen y ⟨hy, hyC⟩
  exact ⟨b, hyb, g, hbg.symm⟩

namespace FrobeniusLiftChart

variable {D}

/-- A point `x` of an open `W` with `i x ∈ C.𝒲` lies in `i⁻¹Õ ⊆ W` for some basic open `Õ` of
the chart `C`. -/
theorem exists_isBasic (C : D.FrobeniusLiftChart) {W : V.Opens} {x : V} (hx : x ∈ W)
    (hxC : D.i x ∈ C.𝒲) : ∃ Õ, C.IsBasic Õ ∧ x ∈ D.i ⁻¹ᵁ Õ ∧ D.i ⁻¹ᵁ Õ ≤ W := by
  have hxW : x ∈ D.i ⁻¹ᵁ D.liftOpen W := by rw [D.preimage_liftOpen]; exact hx
  obtain ⟨g, hg, hxg⟩ := C.isAffineOpen.exists_basicOpen_le (V := D.liftOpen W) ⟨D.i x, hxW⟩ hxC
  refine ⟨_, ⟨g, rfl⟩, hxg, ?_⟩
  rw [← D.preimage_liftOpen W]
  exact D.i.preimage_mono hg

/-- A point `x` of an open `W` with `i x ∈ C₁.𝒲 ∩ C₂.𝒲` lies in `i⁻¹Õ ⊆ W` for some open `Õ`
basic for both charts `C₁` and `C₂`. -/
theorem exists_isBasic₂ (C₁ C₂ : D.FrobeniusLiftChart) {W : V.Opens} {x : V} (hx : x ∈ W)
    (h₁ : D.i x ∈ C₁.𝒲) (h₂ : D.i x ∈ C₂.𝒲) :
    ∃ Õ, (C₁.IsBasic Õ ∧ C₂.IsBasic Õ) ∧ x ∈ D.i ⁻¹ᵁ Õ ∧ D.i ⁻¹ᵁ Õ ≤ W := by
  obtain ⟨Õ, hÕ, hxÕ, hÕW⟩ := C₁.exists_isBasic hx h₁
  obtain ⟨b, hxb, hb⟩ := D.exists_isBasic_basicOpen hÕ.isAffineOpen C₂ hxÕ h₂
  exact ⟨_, ⟨isBasic_basicOpen hÕ b, hb⟩, hxb,
    (D.i.preimage_mono (D.𝒱.basicOpen_le b)).trans hÕW⟩

/-- A point `x` of an open `W` with `i x ∈ C₁.𝒲 ∩ C₂.𝒲 ∩ C₃.𝒲` lies in `i⁻¹Õ ⊆ W` for some open
`Õ` basic for all three charts `C₁`, `C₂` and `C₃`. -/
theorem exists_isBasic₃ (C₁ C₂ C₃ : D.FrobeniusLiftChart) {W : V.Opens} {x : V} (hx : x ∈ W)
    (h₁ : D.i x ∈ C₁.𝒲) (h₂ : D.i x ∈ C₂.𝒲) (h₃ : D.i x ∈ C₃.𝒲) :
    ∃ Õ, (C₁.IsBasic Õ ∧ C₂.IsBasic Õ ∧ C₃.IsBasic Õ) ∧ x ∈ D.i ⁻¹ᵁ Õ ∧ D.i ⁻¹ᵁ Õ ≤ W := by
  obtain ⟨Õ, ⟨hÕ₁, hÕ₂⟩, hxÕ, hÕW⟩ := exists_isBasic₂ C₁ C₂ hx h₁ h₂
  obtain ⟨b, hxb, hb⟩ := D.exists_isBasic_basicOpen hÕ₁.isAffineOpen C₃ hxÕ h₃
  exact ⟨_, ⟨isBasic_basicOpen hÕ₁ b, isBasic_basicOpen hÕ₂ b, hb⟩, hxb,
    (D.i.preimage_mono (D.𝒱.basicOpen_le b)).trans hÕW⟩

/-! ### The glued local splitting of a chart -/

variable (C : D.FrobeniusLiftChart)

/-- The preimages `i⁻¹Õ` of the basic opens `Õ` of `C` form a basis of the opens inside
`i⁻¹ C.𝒲`. -/
theorem isBasis₁ : ∀ W ≤ D.i ⁻¹ᵁ C.𝒲, ∀ x ∈ W,
    ∃ a : {Õ // C.IsBasic Õ}, x ∈ D.i ⁻¹ᵁ a.1 ∧ D.i ⁻¹ᵁ a.1 ≤ W := by
  intro W hW x hx
  obtain ⟨Õ, hÕ, hxÕ, hÕW⟩ := C.exists_isBasic hx (hW hx)
  exact ⟨⟨Õ, hÕ⟩, hxÕ, hÕW⟩

/-- The preimage `i⁻¹Õ` of a basic open `Õ` of `C` is contained in `i⁻¹ C.𝒲`. -/
theorem le₁ : ∀ a : {Õ // C.IsBasic Õ}, D.i ⁻¹ᵁ a.1 ≤ D.i ⁻¹ᵁ C.𝒲 :=
  fun a => D.i.preimage_mono a.2.le

/-- The pieces `C.phiPiece` of the splitting commute with restriction along `i⁻¹Õ' ⊆ i⁻¹Õ`. -/
theorem phiPiece_natural : ∀ (a b : {Õ // C.IsBasic Õ}) (h : D.i ⁻¹ᵁ b.1 ≤ D.i ⁻¹ᵁ a.1)
    (s : Γ(D.K 1, D.i ⁻¹ᵁ a.1)),
    C.phiPiece b.2 ((D.K 1).presheaf.map (homOfLE h).op s) =
      (D.K 1).presheaf.map (homOfLE h).op (C.phiPiece a.2 s) :=
  fun a b h s => C.phiPiece_map a.2 b.2 (D.preimage_le_preimage_iff.1 h) s

/-- **The local Frobenius splitting of a chart**, glued from its pieces. -/
def phi {W : V.Opens} (hW : W ≤ D.i ⁻¹ᵁ C.𝒲) : Γ(D.K 1, W) →+ Γ(D.K 1, W) :=
  glue (fun a : {Õ // C.IsBasic Õ} => D.i ⁻¹ᵁ a.1) C.isBasis₁ C.le₁ (fun a => C.phiPiece a.2)
    C.phiPiece_natural hW

/-- The restriction of `C.phi` to `i⁻¹Õ ⊆ W`, for a basic open `Õ` of `C`, is `C.phiPiece` of
the restriction. -/
theorem phi_spec {W : V.Opens} (hW : W ≤ D.i ⁻¹ᵁ C.𝒲) (s : Γ(D.K 1, W)) {Õ : D.𝒱.Opens}
    (h : C.IsBasic Õ) (hÕ : D.i ⁻¹ᵁ Õ ≤ W) :
    (D.K 1).presheaf.map (homOfLE hÕ).op (C.phi hW s) =
      C.phiPiece h ((D.K 1).presheaf.map (homOfLE hÕ).op s) :=
  glue_spec (fun a : {Õ // C.IsBasic Õ} => D.i ⁻¹ᵁ a.1) C.isBasis₁ C.le₁ (fun a => C.phiPiece a.2)
    C.phiPiece_natural hW s ⟨Õ, h⟩ hÕ

/-- The splitting `C.phi` is `p`-semilinear: `φ (r • s) = r ^ p • φ s`. -/
theorem phi_smul {W : V.Opens} (hW : W ≤ D.i ⁻¹ᵁ C.𝒲) (r : Γ(V, W)) (s : Γ(D.K 1, W)) :
    C.phi hW (r • s) = r ^ p • C.phi hW s :=
  glue_smul (fun a : {Õ // C.IsBasic Õ} => D.i ⁻¹ᵁ a.1) C.isBasis₁ C.le₁ (fun a => C.phiPiece a.2)
    C.phiPiece_natural p (fun a r s => C.phiPiece_smul a.2 r s) hW r s

/-- The splitting `C.phi` commutes with restriction along `W₁ ⊆ W₂`. -/
theorem phi_res {W₁ W₂ : V.Opens} (h₁ : W₁ ≤ D.i ⁻¹ᵁ C.𝒲) (h₂ : W₂ ≤ D.i ⁻¹ᵁ C.𝒲)
    (h : W₁ ≤ W₂) (s : Γ(D.K 1, W₂)) :
    C.phi h₁ ((D.K 1).presheaf.map (homOfLE h).op s) =
      (D.K 1).presheaf.map (homOfLE h).op (C.phi h₂ s) :=
  glue_res (fun a : {Õ // C.IsBasic Õ} => D.i ⁻¹ᵁ a.1) C.isBasis₁ C.le₁ (fun a => C.phiPiece a.2)
    C.phiPiece_natural h₁ h₂ h s

end FrobeniusLiftChart

/-- The preimages `i⁻¹Õ` of the opens `Õ` basic for both `C₁` and `C₂` form a basis of the opens
inside `i⁻¹ C₁.𝒲 ∩ i⁻¹ C₂.𝒲`. -/
theorem isBasis₂ (C₁ C₂ : D.FrobeniusLiftChart) : ∀ W ≤ D.i ⁻¹ᵁ C₁.𝒲 ⊓ D.i ⁻¹ᵁ C₂.𝒲, ∀ x ∈ W,
    ∃ a : {Õ // C₁.IsBasic Õ ∧ C₂.IsBasic Õ}, x ∈ D.i ⁻¹ᵁ a.1 ∧ D.i ⁻¹ᵁ a.1 ≤ W := by
  intro W hW x hx
  obtain ⟨Õ, hÕ, hxÕ, hÕW⟩ :=
    FrobeniusLiftChart.exists_isBasic₂ C₁ C₂ hx (hW hx).1 (hW hx).2
  exact ⟨⟨Õ, hÕ⟩, hxÕ, hÕW⟩

/-- The preimage `i⁻¹Õ` of an open `Õ` basic for `C₁` and `C₂` is contained in
`i⁻¹ C₁.𝒲 ∩ i⁻¹ C₂.𝒲`. -/
theorem le₂ (C₁ C₂ : D.FrobeniusLiftChart) : ∀ a : {Õ // C₁.IsBasic Õ ∧ C₂.IsBasic Õ},
    D.i ⁻¹ᵁ a.1 ≤ D.i ⁻¹ᵁ C₁.𝒲 ⊓ D.i ⁻¹ᵁ C₂.𝒲 :=
  fun a => le_inf (D.i.preimage_mono a.2.1.le) (D.i.preimage_mono a.2.2.le)

/-- The pieces `etaPiece C₁ C₂` of the homotopy commute with restriction along
`i⁻¹Õ' ⊆ i⁻¹Õ`. -/
theorem etaPiece_natural (C₁ C₂ : D.FrobeniusLiftChart) :
    ∀ (a b : {Õ // C₁.IsBasic Õ ∧ C₂.IsBasic Õ}) (h : D.i ⁻¹ᵁ b.1 ≤ D.i ⁻¹ᵁ a.1)
    (s : Γ(D.K 1, D.i ⁻¹ᵁ a.1)),
    etaPiece C₁ C₂ b.2.1 b.2.2 ((D.K 1).presheaf.map (homOfLE h).op s) =
      (D.K 0).presheaf.map (homOfLE h).op (etaPiece C₁ C₂ a.2.1 a.2.2 s) :=
  fun a b h s => etaPiece_map C₁ C₂ a.2.1 a.2.2 b.2.1 b.2.2 (D.preimage_le_preimage_iff.1 h) s

/-- **The homotopy between the glued splittings of two charts.** -/
def homotopy (C₁ C₂ : D.FrobeniusLiftChart) {W : V.Opens}
    (hW : W ≤ D.i ⁻¹ᵁ C₁.𝒲 ⊓ D.i ⁻¹ᵁ C₂.𝒲) : Γ(D.K 1, W) →+ Γ(D.K 0, W) :=
  glue (fun a : {Õ // C₁.IsBasic Õ ∧ C₂.IsBasic Õ} => D.i ⁻¹ᵁ a.1) (D.isBasis₂ C₁ C₂)
    (D.le₂ C₁ C₂) (fun a => etaPiece C₁ C₂ a.2.1 a.2.2) (D.etaPiece_natural C₁ C₂) hW

/-- The restriction of `homotopy C₁ C₂` to `i⁻¹Õ ⊆ W`, for an open `Õ` basic for both charts, is
`etaPiece C₁ C₂` of the restriction. -/
theorem homotopy_spec (C₁ C₂ : D.FrobeniusLiftChart) {W : V.Opens}
    (hW : W ≤ D.i ⁻¹ᵁ C₁.𝒲 ⊓ D.i ⁻¹ᵁ C₂.𝒲) (s : Γ(D.K 1, W)) {Õ : D.𝒱.Opens}
    (h₁ : C₁.IsBasic Õ) (h₂ : C₂.IsBasic Õ) (hÕ : D.i ⁻¹ᵁ Õ ≤ W) :
    (D.K 0).presheaf.map (homOfLE hÕ).op (D.homotopy C₁ C₂ hW s) =
      etaPiece C₁ C₂ h₁ h₂ ((D.K 1).presheaf.map (homOfLE hÕ).op s) :=
  glue_spec (fun a : {Õ // C₁.IsBasic Õ ∧ C₂.IsBasic Õ} => D.i ⁻¹ᵁ a.1) (D.isBasis₂ C₁ C₂)
    (D.le₂ C₁ C₂) (fun a => etaPiece C₁ C₂ a.2.1 a.2.2) (D.etaPiece_natural C₁ C₂) hW s
    ⟨Õ, h₁, h₂⟩ hÕ

/-- The homotopy `homotopy C₁ C₂` is `p`-semilinear: `η (r • s) = r ^ p • η s`. -/
theorem homotopy_smul (C₁ C₂ : D.FrobeniusLiftChart) {W : V.Opens}
    (hW : W ≤ D.i ⁻¹ᵁ C₁.𝒲 ⊓ D.i ⁻¹ᵁ C₂.𝒲) (r : Γ(V, W)) (s : Γ(D.K 1, W)) :
    D.homotopy C₁ C₂ hW (r • s) = r ^ p • D.homotopy C₁ C₂ hW s :=
  glue_smul (fun a : {Õ // C₁.IsBasic Õ ∧ C₂.IsBasic Õ} => D.i ⁻¹ᵁ a.1) (D.isBasis₂ C₁ C₂)
    (D.le₂ C₁ C₂) (fun a => etaPiece C₁ C₂ a.2.1 a.2.2) (D.etaPiece_natural C₁ C₂) p
    (fun a r s => etaPiece_smul C₁ C₂ a.2.1 a.2.2 r s) hW r s

/-- The homotopy `homotopy C₁ C₂` commutes with restriction along `W₁ ⊆ W₂`. -/
theorem homotopy_res (C₁ C₂ : D.FrobeniusLiftChart) {W₁ W₂ : V.Opens}
    (h₁ : W₁ ≤ D.i ⁻¹ᵁ C₁.𝒲 ⊓ D.i ⁻¹ᵁ C₂.𝒲) (h₂ : W₂ ≤ D.i ⁻¹ᵁ C₁.𝒲 ⊓ D.i ⁻¹ᵁ C₂.𝒲)
    (h : W₁ ≤ W₂) (s : Γ(D.K 1, W₂)) :
    D.homotopy C₁ C₂ h₁ ((D.K 1).presheaf.map (homOfLE h).op s) =
      (D.K 0).presheaf.map (homOfLE h).op (D.homotopy C₁ C₂ h₂ s) :=
  glue_res (fun a : {Õ // C₁.IsBasic Õ ∧ C₂.IsBasic Õ} => D.i ⁻¹ᵁ a.1) (D.isBasis₂ C₁ C₂)
    (D.le₂ C₁ C₂) (fun a => etaPiece C₁ C₂ a.2.1 a.2.2) (D.etaPiece_natural C₁ C₂) h₁ h₂ h s

/-! ### The identities of the glued splittings -/

/-- **`φ₂ - φ₁ = d ∘ η₁₂`** for the glued splittings of two charts. -/
theorem phi_sub_phi (C₁ C₂ : D.FrobeniusLiftChart) {W : V.Opens}
    (hW : W ≤ D.i ⁻¹ᵁ C₁.𝒲 ⊓ D.i ⁻¹ᵁ C₂.𝒲) (s : Γ(D.K 1, W)) :
    C₂.phi (hW.trans inf_le_right) s - C₁.phi (hW.trans inf_le_left) s =
      (D.d 0).app W (D.homotopy C₁ C₂ hW s) := by
  refine eq_of_forall_basis (fun a : {Õ // C₁.IsBasic Õ ∧ C₂.IsBasic Õ} => D.i ⁻¹ᵁ a.1)
    (D.isBasis₂ C₁ C₂) hW fun a ha => ?_
  rw [map_sub, C₂.phi_spec _ s a.2.2 ha, C₁.phi_spec _ s a.2.1 ha,
    phiPiece_sub_phiPiece C₁ C₂ a.2.1 a.2.2, ← D.homotopy_spec C₁ C₂ hW s a.2.1 a.2.2 ha]
  exact app_presheaf_map (D.d 0) (homOfLE ha) (D.homotopy C₁ C₂ hW s)

/-- **The cocycle relation** for the glued homotopies of three charts. -/
theorem homotopy_add_homotopy (C₁ C₂ C₃ : D.FrobeniusLiftChart) {W : V.Opens}
    (hW : W ≤ D.i ⁻¹ᵁ C₁.𝒲 ⊓ D.i ⁻¹ᵁ C₂.𝒲 ⊓ D.i ⁻¹ᵁ C₃.𝒲) (s : Γ(D.K 1, W)) :
    D.homotopy C₁ C₂ (hW.trans inf_le_left) s +
        D.homotopy C₂ C₃ (hW.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) s =
      D.homotopy C₁ C₃ (hW.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) s := by
  refine eq_of_forall_basis
    (fun a : {Õ // C₁.IsBasic Õ ∧ C₂.IsBasic Õ ∧ C₃.IsBasic Õ} => D.i ⁻¹ᵁ a.1)
    (fun W' hW' x hx => by
      obtain ⟨Õ, hÕ, hxÕ, hÕW⟩ := FrobeniusLiftChart.exists_isBasic₃ C₁ C₂ C₃ hx
        (hW' hx).1.1 (hW' hx).1.2 (hW' hx).2
      exact ⟨⟨Õ, hÕ⟩, hxÕ, hÕW⟩) hW fun a ha => ?_
  rw [map_add, D.homotopy_spec C₁ C₂ _ s a.2.1 a.2.2.1 ha,
    D.homotopy_spec C₂ C₃ _ s a.2.2.1 a.2.2.2 ha, D.homotopy_spec C₁ C₃ _ s a.2.1 a.2.2.2 ha]
  exact etaPiece_add_etaPiece C₁ C₂ C₃ a.2.1 a.2.2.1 a.2.2.2 _

/-- **The glued splitting of a chart represents the inverse Cartier map.** -/
theorem cartierRep_phi (C : D.FrobeniusLiftChart) {W : V.Opens} (hW : W ≤ D.i ⁻¹ᵁ C.𝒲)
    (s : Γ(D.K 1, W)) : D.cartierRep 1 W s (C.phi hW s) := by
  intro W'' hW'' _
  refine D.isInvCartierRep_of_forall_mem 1 W'' _ _ fun y hy => ?_
  have hyW : y ∈ W := (hW'' hy).1
  obtain ⟨Õ, hÕ, hyÕ, hÕW⟩ := C.exists_isBasic hyW (hW hyW)
  have hyP : y ∈ (D.pieceAffine Õ hÕ.isAffineOpen_inf_U : V.Opens) := ⟨hyÕ, (hW'' hy).2⟩
  obtain ⟨g, g', hgg', hyg⟩ := exists_basicOpen_le_affine_inter W''.2
    (D.pieceAffine Õ hÕ.isAffineOpen_inf_U).2 y ⟨hy, hyP⟩
  obtain ⟨G, hGg⟩ : ∃ G : V.affineOpens, (G : V.Opens) = V.basicOpen g :=
    ⟨⟨_, W''.2.basicOpen g⟩, rfl⟩
  have hGP : (G : V.Opens) ≤ (D.pieceAffine Õ hÕ.isAffineOpen_inf_U : V.Opens) :=
    hGg ▸ hgg' ▸ V.basicOpen_le g'
  have hG : (G : V.Opens) ≤ W'' := hGg ▸ V.basicOpen_le g
  refine ⟨G, hG, g, hGg, hGg ▸ hyg, ?_⟩
  intro _
  have key := C.isInvCartierRep_frobeniusForm hÕ G hGP
    (D.e 1 (D.i ⁻¹ᵁ Õ) ((D.K 1).presheaf.map (homOfLE hÕW).op s))
  have hk : (G : V.Opens) ≤ W ⊓ D.U := hG.trans hW''
  have e1 : (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hGP).op
      (D.e 1 (D.i ⁻¹ᵁ Õ) ((D.K 1).presheaf.map (homOfLE hÕW).op s)) =
      (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hG).op
        ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hW'').op
          (D.e 1 W s)) := by
    rw [D.he_res, presheaf_map_map _ _ (homOfLE hk), presheaf_map_map _ _ (homOfLE hk)]
  have e2 : (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hGP).op
      (C.frobeniusForm hÕ (D.e 1 (D.i ⁻¹ᵁ Õ) ((D.K 1).presheaf.map (homOfLE hÕW).op s))) =
      (f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hG).op
        ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hW'').op
          (D.e 1 W (C.phi hW s))) := by
    rw [← C.e_phiPiece, ← C.phi_spec hW s hÕ hÕW, D.he_res, presheaf_map_map _ _ (homOfLE hk),
      presheaf_map_map _ _ (homOfLE hk)]
  rw [e1, e2] at key
  exact key

/-! ### The local Frobenius splittings from a cover by charts -/

/-- **Local Frobenius splittings from charts**: given, for every point `x` of `V`, a chart of the
lifting with a Frobenius lift whose affine open contains `i x`, the glued maps `φ`, `η` of the
charts form local Frobenius splittings of the logarithmic de Rham complex. -/
def localFrobeniusSplittingOfCharts (charts : V → D.FrobeniusLiftChart)
    (hcharts : ∀ x, D.i x ∈ (charts x).𝒲) : D.LocalFrobeniusSplitting where
  Chart := V
  U x := D.i ⁻¹ᵁ (charts x).𝒲
  iSup_U := eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hcharts y⟩
  φ x _ hW := (charts x).phi hW
  φ_smul x _ hW r s := (charts x).phi_smul hW r s
  φ_res x _ _ h₁ h₂ h s := (charts x).phi_res h₁ h₂ h s
  cartierRep_φ x _ hW s := D.cartierRep_phi (charts x) hW s
  η x y _ hW := D.homotopy (charts x) (charts y) hW
  η_smul x y _ hW r s := D.homotopy_smul (charts x) (charts y) hW r s
  η_res x y _ _ h₁ h₂ h s := D.homotopy_res (charts x) (charts y) h₁ h₂ h s
  φ_sub x y _ hW s := D.phi_sub_phi (charts x) (charts y) hW s
  η_add x y z _ hW s := D.homotopy_add_homotopy (charts x) (charts y) (charts z) hW s

/-- **Local Frobenius splittings exist** as soon as every point of `V` lies in a chart of the
lifting with a Frobenius lift. -/
theorem nonempty_localFrobeniusSplitting_of_forall_exists_chart
    (h : ∀ x : V, ∃ C : D.FrobeniusLiftChart, D.i x ∈ C.𝒲) :
    Nonempty D.LocalFrobeniusSplitting :=
  ⟨D.localFrobeniusSplittingOfCharts (fun x => (h x).choose) fun x => (h x).choose_spec⟩

end FrobeniusSplittingData

end MMP.DeRham
