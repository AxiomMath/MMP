module

public import MMP.AlgebraicGeometry.Divisor.SectionPowerInclusion
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformChartBlowUp
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjPointOfRingHom
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections

/-!
# The divisor of zeros of a section of a power of an invertible module

Let `X` be an integral, locally Noetherian, normal, quasi-compact scheme, `L` an invertible
`𝒪_X`-module and `s` a nonzero global section of `L^{⊗ m}`. Writing `L^{⊗ m}` as a divisorial
sheaf `𝒪_X(G)`, multiplication by `s` is multiplication by a rational function, an isomorphism of
`𝒪_X` onto `𝒪_X(G - D) ⊆ 𝒪_X(G)` for an effective divisor `D`: the divisor of zeros of `s`.

## Main results

* `MMP.LcBpf.exists_isSectionDivisor`: a nonzero section has a divisor of zeros.

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  proof of Theorem 2.47
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MMP.Mori
open Stacks.EnriquesSeveriZariski

universe u

namespace MMP.LcBpf

variable {X : Scheme.{u}}

/-- Multiplication by a nonzero global section is a nonzero morphism. -/
theorem sectionHom_ne_zero (M : X.Modules) {σ : Γ(M, ⊤)} (hσ : σ ≠ 0) : sectionHom M σ ≠ 0 := by
  intro h0
  have happ : (sectionHom M σ).val.app (op ⊤) (show Γ(X, ⊤) from 1) =
      (show Γ(X, ⊤) from 1) • M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ :=
    Stacks.NonvanishingTrivialize.unitHomEquiv_symm_app (X := X.toRingedSpace)
      ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm σ) ⊤ (show Γ(X, ⊤) from 1)
  rw [h0] at happ
  have hid : M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ = σ := by
    rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from rfl, M.presheaf.map_id]
    rfl
  rw [hid, one_smul] at happ
  exact hσ happ.symm

variable [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- **A nonzero section has a divisor of zeros.** -/
theorem exists_isSectionDivisor (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {m : ℕ}
    (s : Γ(Stacks.Ample.tensorPowModule X L (m : ℤ), ⊤)) (hs : s ≠ 0) :
    ∃ D, IsSectionDivisor L s D := by
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule X L (m : ℤ)) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule X L _
  obtain ⟨G, ⟨f⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible
    (Stacks.Ample.tensorPowModule X L (m : ℤ))
  set z := (Divisor.divisorialSheafZeroIso (X := X))
  set α : (0 : Divisor X).divisorialSheaf ⟶ G.divisorialSheaf :=
    z.hom ≫ sectionHom _ s ≫ f.inv with hαdef
  have hα : α ≠ 0 := by
    intro h0
    refine sectionHom_ne_zero _ hs ?_
    have : sectionHom _ s = z.inv ≫ α ≫ f.hom := by
      rw [hαdef]
      simp
    rw [this, h0]
    simp
  obtain ⟨C, hC, eC, hαC⟩ := exists_iso_comp_divisorialSheafInclusion α hα
  refine ⟨G - C, G, f.symm, ?_⟩
  rw [sub_sub_cancel]
  refine ⟨hC, z.symm ≪≫ eC, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← hαC, hαdef, Iso.inv_hom_id_assoc]

section Powers

open Stacks.Ample Stacks.RelativeVeryAmple

omit [IsIntegral X] in
/-- `𝒪_X(E)^{⊗ n} ≅ 𝒪_X(nE)` for a Cartier divisor `E`, for `n ≥ 0`. -/
theorem nonempty_tensorPowModule_iso_divisorialSheaf (E : Divisor X) (hE : E.IsCartier)
    [IsInvertibleModule X E.divisorialSheaf] (n : ℕ) :
    Nonempty (tensorPowModule X E.divisorialSheaf (n : ℤ) ≅ (n • E).divisorialSheaf) := by
  induction n with
  | zero =>
    exact ⟨tensorPowModuleZeroIso X E.divisorialSheaf ≪≫
      (eqToIso rfl : unitModule X ≅ MMP.Mori.structureSheafModule X) ≪≫
      (Divisor.divisorialSheafZeroIso (X := X)).symm ≪≫ eqToIso (by rw [zero_nsmul])⟩
  | succ n ih =>
    obtain ⟨p⟩ := ih
    exact ⟨tensorPowModuleCongr X E.divisorialSheaf
        (show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring) ≪≫
      (tensorPowModuleAddIso X E.divisorialSheaf (n : ℤ) 1).symm ≪≫
      tensorModulesMapIso X p (tensorPowModuleOneIso X E.divisorialSheaf) ≪≫
      (hE.nsmul n).divisorialSheafTensorIso hE ≪≫ eqToIso (by rw [succ_nsmul])⟩

/-- **The divisor of zeros of `s` is linearly equivalent to `m M`** when `𝒪_X(M) ≅ L`: there is
a rational function `ψ` with `m M = D + div ψ`. -/
theorem IsSectionDivisor.exists_eq_add_principalDivisor (hcart : ∀ D : Divisor X, D.IsCartier)
    {L : X.Modules} [IsInvertibleModule X L] (M : Divisor X) (eM : M.divisorialSheaf ≅ L)
    {m : ℕ} {s : Γ(tensorPowModule X L (m : ℤ), ⊤)} {D : Divisor X}
    (hD : IsSectionDivisor L s D) :
    ∃ ψ : (RationalFunctions X)ˣ, m • M = D + principalDivisor ψ := by
  have := (hcart M).isInvertibleModule_divisorialSheaf
  obtain ⟨G, ε, -, e, -⟩ := hD
  obtain ⟨p⟩ := nonempty_tensorPowModule_iso_divisorialSheaf M (hcart M) m
  have h1 := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (p.symm ≪≫
      Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorPowModuleIsoOfIsoInt X _ _ eM
        (m : ℤ) ≪≫ ε)
  have h2 := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e.symm ≪≫ (eqToIso rfl : unitModule X ≅ MMP.Mori.structureSheafModule X) ≪≫
      (Divisor.divisorialSheafZeroIso (X := X)).symm)
  have h3 : G.LinearlyEquivalent D := by
    have := h2.add (Divisor.LinearlyEquivalent.refl D)
    simpa using this
  obtain ⟨ψ, hψ⟩ := h1.trans h3
  exact ⟨ψ, by rw [← hψ]; abel⟩

/-- **The negative powers of `L = 𝒪_X(M)`**: `𝒪_X ⊗ L^{⊗ -r} ≅ 𝒪_X(-rM)`, all divisors being
Cartier. -/
theorem nonempty_twist_neg_iso_divisorialSheaf (hcart : ∀ D : Divisor X, D.IsCartier)
    (L : X.Modules) [IsInvertibleModule X L] (M : Divisor X) (eM : M.divisorialSheaf ≅ L)
    (r : ℕ) :
    Nonempty (twist L (unitModule X) (-(r : ℤ)) ≅ (-((r : ℤ) • M)).divisorialSheaf) := by
  have := (hcart M).isInvertibleModule_divisorialSheaf
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowModule X L (-(r : ℤ))) := isInvertibleModule_tensorPowModule X L _
  obtain ⟨A, ⟨fA⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible
    (tensorPowModule X L (-(r : ℤ)))
  obtain ⟨p⟩ := nonempty_tensorPowModule_iso_divisorialSheaf M (hcart M) r
  have t : (A + r • M).divisorialSheaf ≅ (0 : Divisor X).divisorialSheaf :=
    ((hcart A).divisorialSheafTensorIso (hcart _)).symm ≪≫
      tensorModulesMapIso X fA (p.symm ≪≫
        Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorPowModuleIsoOfIsoInt X _ _ eM r) ≪≫
      tensorPowModuleAddIso X L (-(r : ℤ)) r ≪≫
      tensorPowModuleCongr X L (show -(r : ℤ) + r = 0 by ring) ≪≫
      tensorPowModuleZeroIso X L ≪≫
      (eqToIso rfl : unitModule X ≅ MMP.Mori.structureSheafModule X) ≪≫
      (Divisor.divisorialSheafZeroIso (X := X)).symm
  have h := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso t
  have hA : A.LinearlyEquivalent (-((r : ℤ) • M)) := by
    have := h.add (Divisor.LinearlyEquivalent.refl (-((r : ℤ) • M)))
    rw [natCast_zsmul] at this ⊢
    simpa using this
  exact ⟨Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _ ≪≫ fA.symm ≪≫
      hA.divisorialSheafIso⟩

/-- **Multiplication by `s^k` is the inclusion `𝒪_X(-rM - kD) ⊆ 𝒪_X(-rM)`.** Let `𝒪_X(M) ≅ L`
and let `D` be the divisor of zeros of a section `s` of `L^{⊗ m}`, every divisor being Cartier.
Then multiplication by `s^k`, from `L^{⊗ -(r + km)}` to `L^{⊗ -r}`, is identified with the
inclusion `𝒪_X(-rM - kD) ⊆ 𝒪_X(-rM)`. -/
theorem exists_iso_chain_eq_divisorialSheafInclusion (hcart : ∀ D : Divisor X, D.IsCartier)
    (L : X.Modules) [IsInvertibleModule X L] (M : Divisor X) (eM : M.divisorialSheaf ≅ L)
    {m : ℕ} (s : Γ(tensorPowModule X L (m : ℤ), ⊤)) {D : Divisor X}
    (hD : IsSectionDivisor L s D) (r k : ℕ) :
    ∃ (e₂ : twist L (unitModule X) (-(r : ℤ)) ≅ (-((r : ℤ) • M)).divisorialSheaf)
      (e₁ : twist L (unitModule X) (descend m (-(r : ℤ)) k) ≅
        (-((r : ℤ) • M) - (k : ℤ) • D).divisorialSheaf)
      (h : -((r : ℤ) • M) - (k : ℤ) • D ≤ -((r : ℤ) • M)),
      chain L s (unitModule X) (-(r : ℤ)) k ≫ e₂.hom =
        e₁.hom ≫ Divisor.divisorialSheafInclusion h := by
  obtain ⟨e₂⟩ := nonempty_twist_neg_iso_divisorialSheaf hcart L M eM r
  obtain ⟨e₁, h, w⟩ := exists_iso_chain_eq_divisorialSheafInclusion_of_iso L s hD _ e₂ k
  exact ⟨e₂, e₁, h, w⟩

end Powers

end MMP.LcBpf
