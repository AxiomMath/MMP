module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.SdltAdjointPair
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.MMP.Fourfold.Preadmissible.ConductorDescent
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness

/-!
# Surface preadmissible systems descend on the whole sdlt union

Let `(T, Δ; L)` be a projective sdlt adjoint surface pair over `ℂ`, with normalization components
`νᵢ : Tᵢ ⟶ T` carrying the boundaries `Θᵢ = Cᵢ + Δᵢ`, and let `pᵢ : Yᵢ ⟶ Tᵢ` be projective
birational morphisms from `ℚ`-factorial normal projective surfaces with `Bᵢ` the crepant boundary
of `(Tᵢ, Θᵢ)` on `Yᵢ`, so that `K_{Yᵢ} + Bᵢ = pᵢ^*(νᵢ^*L)` and `(Yᵢ, Bᵢ)` is dlt. Then there is
`m₀ > 0` such that in every even degree `m` divisible by `m₀` every preadmissible section system
`(sᵢ)` on the `Yᵢ` is the pull-back of a unique section of `𝒪_T(mL)`; and if preadmissible systems
generate `𝒪_{Yᵢ}(m(K_{Yᵢ} + Bᵢ))` at every point of every `Yᵢ`, the descended sections generate
`𝒪_T(mL)` at every point of `T`.

The sections descend to the normal surfaces `Tᵢ` by `pᵢ_* 𝒪_{Yᵢ} = 𝒪_{Tᵢ}` and the projection
formula. The conductor curves are floor curves of the `(Yᵢ, Bᵢ)`, and surface residue adjunction,
together with the opposite branch residues of the sdlt pair, makes the branch exchange a crepant
identification of their adjunction pairs; preadmissibility therefore identifies the two even
residues, the semismooth conductor equalizer descends the branch functions off a finite set, and
the `S₂` property of `T` extends the section across it.

## Main results

* `MMP.Fourfold.IsSdltAdjointPair.exists_existsUnique_pullback_eq_of_mem_preadmissibleSections`.

## Implementation notes

As in `MMP.Fourfold.IsSdltAdjointPair`, a section of `𝒪_T(mL)` is a family `t = (tᵢ)ᵢ` of
rational `m`-canonical forms on the normalization components which is, near every point of `T`,
the product `ν^*f · g` of a function `f` on an open `U ⊆ T` and a local generator `g` of
`𝒪_T(mL)` on `U` (`MMP.Fourfold.IsAdjointGeneratorOn`, together with sign-`1` log residue
presentations `MMP.Fourfold.IsLogResiduePresentation` along the conductor curves over the double
locus, also along a curve glued to itself, exactly as in the generator field of
`MMP.Fourfold.IsSdltAdjointPair`); it generates `𝒪_T(mL)` at `x` when `f`
can be taken to be a unit near `x`. Section systems on the `Yᵢ` are the preadmissible subspace
`MMP.Fourfold.preadmissibleSections` of any residue-restriction system
`MMP.Fourfold.ResidueRestriction` for the pairs `(Yᵢ, Bᵢ)` in degree `m`, which records that the
`(Yᵢ, Bᵢ)` are projective rational dlt surface pairs, that `m` is even and that the stratum
adjoints are Cartier. "Sufficiently divisible" is "divisible by some `m₀ > 0`"; it makes `mL`
Cartier, which in the general-dimensional
`MMP.Fourfold.IsSdltAdjointPair.existsUnique_pullback_eq_of_mem_preadmissibleSections` is a
hypothesis. The descent of `t` to `(sᵢ)` is pull-back of forms along the function-field
extensions of the `pᵢ` (`MMP.Mori.pullbackRationalPluriForms`).

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Section 5.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori hiding IsPair
open MMP.Flips

/-- **Powers of rational pluriforms.** On an integral scheme of dimension `d`, there is
a `c`-th power map from rational `a`-canonical forms to rational `ac`-canonical forms sending
`f ω^{⊗a}` to `f^c ω^{⊗ac}` for every rational function `f` and every top form `ω`. -/
private theorem exists_powForm {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) (a c : ℕ) :
    letI := functionFieldAlgebra sX
    ∃ P : RationalPluriForms sX d a → RationalPluriForms sX d ((a * c : ℕ) : ℤ),
      ∀ (f : X.functionField) (ω : ⋀[X.functionField]^d Ω[X.functionField⁄ℂ]),
        P (f • formPow ω a) = f ^ c • formPow ω (a * c) := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  refine ⟨fun τ => ((ZTensorPower.basis b a).repr τ ()) ^ c • formPow (b ()) (a * c),
    fun f ω => ?_⟩
  have hpow : ∀ e : ℕ, formPow ω e = (b.repr ω ()) ^ e • formPow (b ()) e := fun e => by
    conv_lhs => rw [← basis_unit_repr_smul b ω]
    rw [formPow_smul]
  simp only
  rw [hpow a, smul_smul, repr_smul_formPow, hpow (a * c), smul_smul, mul_pow, ← pow_mul,
    mul_comm a c]

/-- The `c`-th power of a local generator of `𝒪_X(a(K_X + Θ))` on `U` is a local generator of
`𝒪_X(ac(K_X + Θ))` on `U`. -/
private theorem generatesOn_powForm {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d)
    {Θ : QDivisor X} {a c : ℕ} {U : X.Opens} {s : RationalPluriForms sX d a}
    (hs : GeneratesOn Θ a U s)
    (Pw : RationalPluriForms sX d a → RationalPluriForms sX d ((a * c : ℕ) : ℤ))
    (hPw : letI := functionFieldAlgebra sX
      ∀ (f : X.functionField) (ω : ⋀[X.functionField]^d Ω[X.functionField⁄ℂ]),
        Pw (f • formPow ω a) = f ^ c • formPow ω (a * c)) :
    GeneratesOn Θ (a * c) U (Pw s) := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  set f := (ZTensorPower.basis b a).repr s () with hf_def
  have hf0 : f ≠ 0 := repr_ne_zero_of_ne_zero b hs.1
  have hP : Pw s = f ^ c • formPow (b ()) (a * c) := by
    rw [eq_repr_smul_formPow b s]; exact hPw _ _
  have hP0 : Pw s ≠ 0 := by
    rw [hP, ← ZTensorPower.basis_natCast]
    exact smul_ne_zero (pow_ne_zero _ hf0) ((ZTensorPower.basis b _).ne_zero ())
  refine ⟨hP0, fun Γ hΓ => ?_⟩
  obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd) b
  have e1 := hs.2 Γ hΓ
  rw [hNΓ _ _ hs.1, ← hf_def] at e1
  rw [hNΓ _ _ hP0, hP, repr_smul_formPow, ← zpow_natCast, ord_zpow _ hf0]
  push_cast at e1 ⊢
  linear_combination (c : ℚ) * e1

/-- A residue presentation of `s` along `P` with sign `ε` gives one of the `c`-th power of `s`,
with sign `ε ^ c`. -/
private theorem isLogResiduePresentation_powForm {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n a c : ℕ} {i : N.ι} {P : Mori.PrimeDivisor (N.X i)}
    {V : T.Opens} {hP : (N.n i).base P.genericPoint ∈ V} {α : Fin (n - 1) → Γ(T, V)}
    {g : Γ(T, V)} {ε ε' : ℤ} {s : RationalPluriForms (N.n i ≫ sT) n a}
    (h : IsLogResiduePresentation N n a i P V hP α g ε s)
    (Pw : RationalPluriForms (N.n i ≫ sT) n a →
      RationalPluriForms (N.n i ≫ sT) n ((a * c : ℕ) : ℤ))
    (hPw : letI := functionFieldAlgebra (N.n i ≫ sT)
      ∀ (f : (N.X i).functionField) (ω : ⋀[(N.X i).functionField]^n Ω[(N.X i).functionField⁄ℂ]),
        Pw (f • formPow ω a) = f ^ c • formPow ω (a * c))
    (hε : ε ^ c = ε' := by simp) :
    IsLogResiduePresentation N n (a * c) i P V hP α (g ^ c) ε' (Pw s) := by
  subst hε
  obtain ⟨z, h', hz, hs, hda, hres⟩ := h
  refine ⟨z, h' ^ c, hz, ?_, hda, ?_⟩
  · rw [hs, map_pow]
    exact hPw _ _
  · beta_reduce at hres ⊢
    simp only [map_pow, hres, mul_pow]
    push_cast
    rfl

/-- Local generators of `𝒪_T(m₁L)` with sign-one residue presentations give local generators of
the same kind in every degree divisible by `m₁`: their `(m / m₁)`-th powers. -/
private theorem exists_generator_of_dvd {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Θ : ∀ i, QDivisor (N.X i)} {m₁ : ℕ}
    (hdim : ∀ i, topologicalKrullDim (N.X i) = n)
    (hgen : ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (s : ∀ i, RationalPluriForms (N.n i ≫ sT) n m₁),
      IsAdjointGeneratorOn N n m₁ Θ U s ∧
        ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
          (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
          ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V))
            (g : Γ(T, V)), IsLogResiduePresentation N n m₁ i P V hP a g 1 (s i))
    {m : ℕ} (hm : m₁ ∣ m) :
    ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (s : ∀ i, RationalPluriForms (N.n i ≫ sT) n m),
      IsAdjointGeneratorOn N n m Θ U s ∧
        ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
          (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
          ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V))
            (g : Γ(T, V)), IsLogResiduePresentation N n m i P V hP a g 1 (s i) := by
  obtain ⟨c, rfl⟩ := hm
  have : ∀ i, LocallyOfFiniteType (N.n i ≫ sT) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  choose Pw hPw using fun i => exists_powForm (sX := N.n i ≫ sT) (hdim i) m₁ c
  intro x
  obtain ⟨U, hxU, s, ⟨hgo, hres⟩, hself⟩ := hgen x
  refine ⟨U, hxU, fun i => Pw i (s i),
    ⟨fun i => generatesOn_powForm (hdim i) (hgo i) (Pw i) (hPw i),
      fun i j P P' h₁ h₂ h₃ h₄ => ?_⟩, fun i P h₁ h₂ => ?_⟩
  · obtain ⟨V, hP, hP', a, g, hpr, hpr'⟩ := hres i j P P' h₁ h₂ h₃ h₄
    exact ⟨V, hP, hP', a, g ^ c, isLogResiduePresentation_powForm hpr (Pw i) (hPw i),
      isLogResiduePresentation_powForm hpr' (Pw j) (hPw j) (pow_mul _ _ _).symm⟩
  · obtain ⟨V, hP, a, g, hpr⟩ := hself i P h₁ h₂
    exact ⟨V, hP, a, g ^ c, isLogResiduePresentation_powForm hpr (Pw i) (hPw i)⟩

/-- **Surface preadmissible systems descend on the whole sdlt union.** Let `(T, Δ; L)` be a
projective sdlt adjoint surface pair over `ℂ` (`MMP.Fourfold.IsSdltAdjointPair` of dimension `2`)
with normalization components `νᵢ : Tᵢ ⟶ T` and boundaries `Θᵢ = Cᵢ + Δᵢ`. Let `pᵢ : Yᵢ ⟶ Tᵢ` be
projective birational morphisms from `ℚ`-factorial normal surfaces (`MMP.Fourfold.IsQFactorial`)
with `Bᵢ` the crepant boundary of `(Tᵢ, Θᵢ)` on `Yᵢ` (`MMP.Mori.IsCrepantBoundary`). Then there
is `m₀ > 0` such that for every even `m` divisible by `m₀` and every residue-restriction system
`R` for the pairs `(Yᵢ, Bᵢ)` in degree `m` (`MMP.Fourfold.ResidueRestriction`):
* every preadmissible system `s ∈ MMP.Fourfold.preadmissibleSections R` is, componentwise, the
  pull-back `pᵢ^* tᵢ` of a unique section `t` of `𝒪_T(mL)`, i.e. of a unique family `t` of
  rational `m`-canonical forms on the `Tᵢ` which near every point of `T` is `ν^*f · g` for a
  function `f` and a local generator `g` (`MMP.Fourfold.IsAdjointGeneratorOn`) whose Poincaré
  residue along every conductor curve over the double locus has sign `1`
  (`MMP.Fourfold.IsLogResiduePresentation`), as in `MMP.Fourfold.IsSdltAdjointPair`;
* if preadmissible systems generate `𝒪_{Yᵢ}(m(K_{Yᵢ} + Bᵢ))` at every point of every `Yᵢ`, then
  for every point `x ∈ T` there is a preadmissible system whose descended section is, near `x`, a
  unit times a local generator of `𝒪_T(mL)`. -/
@[mmp "lem_mmp_surface_preadmissible_conductor_descent"]
public theorem IsSdltAdjointPair.exists_existsUnique_pullback_eq_of_mem_preadmissibleSections
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 2 Δ Θ)
    {Y : N.ι → Scheme.{0}} [∀ i, IsIntegral (Y i)] [∀ i, IsLocallyNoetherian (Y i)]
    [∀ i, IsNormal (Y i)] (p : ∀ i, Y i ⟶ N.X i) [∀ i, IsDominant (p i)]
    (hproj : ∀ i, IsProjectiveMorphism (p i)) (hQ : ∀ i, IsQFactorial (p i ≫ N.n i ≫ sT))
    {B : ∀ i, QDivisor (Y i)}
    (hcrep : ∀ i, ∃ (K : Divisor (N.X i)) (hY : IsNormalVariety ℂ (p i ≫ N.n i ≫ sT))
      (hp : IsBirationalMorphism (p i)),
      IsCrepantBoundary (N.n i ≫ sT) 2 K (Θ i) (p i) hY hp (B i)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → Even m →
      ∀ R : ResidueRestriction (fun i => p i ≫ N.n i ≫ sT) B 2 m,
      (∀ s ∈ preadmissibleSections R,
        ∃! t : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m,
          (∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m)
            (f : Γ(T, U)), (IsAdjointGeneratorOn N 2 m Θ U g ∧
                ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
                  (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
                  ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V)
                    (a : Fin (2 - 1) → Γ(T, V)) (g' : Γ(T, V)),
                    IsLogResiduePresentation N 2 m i P V hP a g' 1 (g i)) ∧
              ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
                t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) • g i) ∧
          ∀ i, pullbackRationalPluriForms (N.n i ≫ sT) (p i) (t i) = (s i : _)) ∧
      ((∀ (i : N.ι) (y : Y i), ∃ s ∈ preadmissibleSections R, ∃ V : (Y i).Opens, y ∈ V ∧
          GeneratesOn (B i) m V ((s i : logPluricanonicalSections (p i ≫ N.n i ≫ sT) 2 m (B i)) :
            RationalPluriForms (p i ≫ N.n i ≫ sT) 2 m)) →
        ∀ x : T, ∃ s ∈ preadmissibleSections R, ∃ (t : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m)
          (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m) (f : Γ(T, U)),
          IsUnit f ∧ (IsAdjointGeneratorOn N 2 m Θ U g ∧
            ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
              (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
              ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V)
                (a : Fin (2 - 1) → Γ(T, V)) (g' : Γ(T, V)),
                IsLogResiduePresentation N 2 m i P V hP a g' 1 (g i)) ∧
          (∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) • g i) ∧
          ∀ i, pullbackRationalPluriForms (N.n i ≫ sT) (p i) (t i) = (s i : _)) := by
  obtain ⟨m₀, hm₀, -, hgen⟩ := h.exists_isAdjointGeneratorOn
  have hdim : ∀ i, topologicalKrullDim (N.X i) = (2 : ℕ) := fun i => by
    obtain ⟨K, hK⟩ := h.exists_isDltPair i
    exact hK.1.2.1.1
  refine ⟨m₀, hm₀, fun m hm _ R => ?_⟩
  have H := h.existsUnique_pullback_eq_of_mem_preadmissibleSections p hproj hcrep R
    (exists_generator_of_dvd hdim hgen hm)
  exact ⟨fun s hs => (H.1 s hs).1, H.2⟩

end MMP.Fourfold
