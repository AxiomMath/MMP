module

public import MMP.AlgebraicGeometry.Divisor.Basic
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint

/-!
# Oriented coefficients on the double surfaces of an snc divisor

Let `Z` be a smooth projective fourfold and `B = ∑ᵢ Eᵢ` a reduced snc divisor on `Z`. A *double
surface* of `B` is a connected component `S` of an intersection `Eᵢ ∩ Eⱼ` of two distinct
components, recorded together with the ordered pair `(i, j)`. An *oriented surface coefficient
system* is a family of rational numbers `a_{ij,S}`, one for each double surface, with
`a_{ji,S} = -a_{ij,S}`. Its divisor on `Eᵢ` is the `ℚ`-divisor
`Zᵢ(a) = ∑_{j ≠ i} ∑_{S ⊆ Eᵢ ∩ Eⱼ} a_{ij,S} S`. At a connected subset `T` of `Eᵢ ∩ Eⱼ` (for
instance a connected component of a triple intersection `Eᵢ ∩ Eⱼ ∩ Eₖ`), `a_{ij,T}` is the
coefficient of the unique double surface containing `T`.

## Main definitions

* `MMP.Fourfold.DoubleSurface`: a double surface `S ⊆ Eᵢ ∩ Eⱼ` of a divisor, with its ordered
  pair of components; `MMP.Fourfold.DoubleSurface.swap` exchanges the pair.
* `MMP.Fourfold.orientedSurfaceCoefficients`: the `ℚ`-space of oriented surface coefficient
  systems, `a_{ji,S} = -a_{ij,S}`.
* `MMP.Fourfold.surfaceCoefficientDivisor`: the divisor `Zᵢ(a)` on the component `Eᵢ`.
* `MMP.Fourfold.DoubleSurface.through`, `MMP.Fourfold.coeffAlong`: the double surface
  containing a nonempty connected subset `T ⊆ Eᵢ ∩ Eⱼ`, and the coefficient `a_{ij,T}`.

## Main results

* `MMP.Fourfold.DoubleSurface.disjoint_carrier`: distinct double surfaces of the same pair are
  disjoint.
* `MMP.Fourfold.DoubleSurface.finite_setOf_carrier`: on a Noetherian scheme each `Eᵢ ∩ Eⱼ` has
  finitely many connected components.
* `MMP.Fourfold.coeff_surfaceCoefficientDivisor`: on a Noetherian scheme the coefficient of
  `Zᵢ(a)` at a prime divisor `P` of `Eᵢ` is the sum of the `a_{ij,S}` over the double surfaces
  `S ⊆ Eᵢ ∩ Eⱼ` whose generic point is that of `P`.
* `MMP.Fourfold.coeffAlong_eq`: `a_{ij,T}` is the coefficient of the double surface through any
  point of `T`.

## Implementation notes

* The components `Eᵢ` of `B` are the prime divisors with nonzero coefficient in `B`; they index
  themselves, so the labelling `i = 1, …, s` is not recorded. The definitions only use the
  components of `B`, so they are stated for any divisor on any scheme; the smooth projective
  fourfold and the reduced snc condition are the setting in which they are used.
* The connected components are taken in the Zariski topology of `Z`, of the closed set
  `Eᵢ ∩ Eⱼ`. A prime divisor `P` of the scheme `Eᵢ` is the surface `S` when the closure of the
  image in `Z` of its generic point is `S`; for an snc divisor every double surface is a smooth
  integral surface, hence of this form for exactly one `P`.
* An oriented system is a function on all double surfaces, with `a_{ii,S}` not defined since
  double surfaces have distinct components.
* `Zᵢ(a)` is the finitely supported function of its coefficients when the set of prime divisors
  with nonzero coefficient is finite, which holds on every Noetherian scheme
  (`MMP.Fourfold.finite_support_surfaceCoefficientCoeff`), and the zero divisor otherwise.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Fourfold

open MMP.Mori

variable {Z : Scheme.{u}} (B : Divisor Z)

/-! ### Double surfaces -/

/-- A *double surface* of the divisor `B = ∑ Eᵢ`: an ordered pair `(Eᵢ, Eⱼ)` of distinct
components of `B` together with a connected component `S` of `Eᵢ ∩ Eⱼ`. -/
@[mmp "def_mmp_conductor_surface_coefficients"]
structure DoubleSurface where
  /-- The first component `Eᵢ`. -/
  fst : Mori.PrimeDivisor Z
  /-- The second component `Eⱼ`. -/
  snd : Mori.PrimeDivisor Z
  fst_mem : fst ∈ B.support
  snd_mem : snd ∈ B.support
  fst_ne_snd : fst ≠ snd
  /-- The surface `S`, a connected component of `Eᵢ ∩ Eⱼ`. -/
  carrier : Set Z
  isComponent : ∃ x ∈ fst.support ∩ snd.support,
    connectedComponentIn (fst.support ∩ snd.support) x = carrier

namespace DoubleSurface

variable {B}

/-- Two double surfaces with the same ordered pair of components and the same surface are equal. -/
@[ext]
theorem ext {σ τ : DoubleSurface B} (h₁ : σ.fst = τ.fst) (h₂ : σ.snd = τ.snd)
    (h₃ : σ.carrier = τ.carrier) : σ = τ := by
  cases σ
  cases τ
  cases h₁
  cases h₂
  cases h₃
  rfl

/-- A double surface `S` of `(Eᵢ, Eⱼ)` is contained in `Eᵢ ∩ Eⱼ`. -/
theorem carrier_subset (σ : DoubleSurface B) : σ.carrier ⊆ σ.fst.support ∩ σ.snd.support := by
  obtain ⟨x, -, hx⟩ := σ.isComponent
  exact hx ▸ connectedComponentIn_subset _ x

/-- A double surface is nonempty. -/
theorem carrier_nonempty (σ : DoubleSurface B) : σ.carrier.Nonempty := by
  obtain ⟨x, hx, h⟩ := σ.isComponent
  exact h ▸ ⟨x, mem_connectedComponentIn hx⟩

/-- A double surface is the connected component of `Eᵢ ∩ Eⱼ` of each of its points. -/
theorem carrier_eq_connectedComponentIn (σ : DoubleSurface B) {y : Z} (hy : y ∈ σ.carrier) :
    σ.carrier = connectedComponentIn (σ.fst.support ∩ σ.snd.support) y := by
  obtain ⟨x, -, hx⟩ := σ.isComponent
  rw [← hx] at hy ⊢
  exact connectedComponentIn_eq hy

/-- Distinct double surfaces of the same ordered pair of components are disjoint. -/
theorem disjoint_carrier {σ τ : DoubleSurface B} (h₁ : σ.fst = τ.fst) (h₂ : σ.snd = τ.snd)
    (hne : σ ≠ τ) : Disjoint σ.carrier τ.carrier := by
  rw [Set.disjoint_iff]
  rintro y ⟨hσ, hτ⟩
  refine hne (ext h₁ h₂ ?_)
  rw [σ.carrier_eq_connectedComponentIn hσ, τ.carrier_eq_connectedComponentIn hτ, h₁, h₂]

/-- The same surface with the ordered pair of components exchanged: `S ⊆ Eⱼ ∩ Eᵢ`. -/
def swap (σ : DoubleSurface B) : DoubleSurface B where
  fst := σ.snd
  snd := σ.fst
  fst_mem := σ.snd_mem
  snd_mem := σ.fst_mem
  fst_ne_snd := σ.fst_ne_snd.symm
  carrier := σ.carrier
  isComponent := by
    obtain ⟨x, hx, h⟩ := σ.isComponent
    exact ⟨x, Set.inter_comm _ _ ▸ hx, by rwa [Set.inter_comm]⟩

/-- The first component of the swapped double surface is the second component. -/
@[simp] theorem swap_fst (σ : DoubleSurface B) : σ.swap.fst = σ.snd := rfl

/-- The second component of the swapped double surface is the first component. -/
@[simp] theorem swap_snd (σ : DoubleSurface B) : σ.swap.snd = σ.fst := rfl

/-- Swapping the components does not change the surface. -/
@[simp] theorem swap_carrier (σ : DoubleSurface B) : σ.swap.carrier = σ.carrier := rfl

/-- Swapping the components twice gives back the double surface. -/
@[simp] theorem swap_swap (σ : DoubleSurface B) : σ.swap.swap = σ := ext rfl rfl rfl

/-- Swapping the components is an involution on double surfaces. -/
theorem swap_involutive : Function.Involutive (swap (B := B)) := swap_swap

/-- Swapping the components is injective on double surfaces. -/
theorem swap_injective : Function.Injective (swap (B := B)) := swap_involutive.injective

/-- In a Noetherian space every closed set has finitely many connected components. -/
theorem finite_connectedComponentIn {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    {F : Set X} (hF : IsClosed F) : {S | ∃ x ∈ F, connectedComponentIn F x = S}.Finite := by
  obtain ⟨T, hT, -, hirr, hFT⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  classical
  refine (hT.image fun t =>
    if h : t.Nonempty then connectedComponentIn F h.some else ∅).subset ?_
  rintro S ⟨x, hx, rfl⟩
  have hx' : x ∈ ⋃₀ T := hFT ▸ hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hx'
  have htF : t ⊆ F := fun y hy => hFT ▸ Set.mem_sUnion_of_mem hy ht
  have hsub := (hirr t ht).2.isPreconnected.subset_connectedComponentIn hxt htF
  have hne : t.Nonempty := ⟨x, hxt⟩
  refine ⟨t, ht, ?_⟩
  simp only [hne, ↓reduceDIte]
  exact (connectedComponentIn_eq (hsub hne.some_mem)).symm

/-- On a Noetherian scheme, for fixed components `Eᵢ`, `Eⱼ`, the surfaces of the double surfaces
of `(Eᵢ, Eⱼ)` form a finite set: `Eᵢ ∩ Eⱼ` has finitely many connected components. -/
theorem finite_setOf_carrier [NoetherianSpace Z] (E E' : Mori.PrimeDivisor Z) :
    {S : Set Z | ∃ σ : DoubleSurface B, σ.fst = E ∧ σ.snd = E' ∧ σ.carrier = S}.Finite := by
  refine (finite_connectedComponentIn
    (E.idealSheaf.support.isClosed.inter E'.idealSheaf.support.isClosed)).subset ?_
  rintro S ⟨σ, rfl, rfl, rfl⟩
  exact σ.isComponent

end DoubleSurface

/-! ### Oriented coefficient systems -/

/-- The *oriented surface coefficient systems* of `B = ∑ Eᵢ`: families of rational numbers
`a_{ij,S}`, one for each connected component `S` of each `Eᵢ ∩ Eⱼ` with `i ≠ j`, such that
`a_{ji,S} = -a_{ij,S}`. They form a `ℚ`-subspace of all families. -/
@[mmp "def_mmp_conductor_surface_coefficients"]
def orientedSurfaceCoefficients : Submodule ℚ (DoubleSurface B → ℚ) where
  carrier := {a | ∀ σ, a σ.swap = -a σ}
  add_mem' {a b} ha hb σ := by simp [ha σ, hb σ, add_comm]
  zero_mem' σ := by simp
  smul_mem' c a ha σ := by simp [ha σ]

/-- A family `a` is an oriented surface coefficient system iff `a_{ji,S} = -a_{ij,S}` for every
double surface. -/
theorem mem_orientedSurfaceCoefficients {a : DoubleSurface B → ℚ} :
    a ∈ orientedSurfaceCoefficients B ↔ ∀ σ, a σ.swap = -a σ := Iff.rfl

/-! ### The divisor of a coefficient system on a component -/

variable {B}

/-- The coefficient of `Zᵢ(a)` at a prime divisor `P` of the component `E = Eᵢ`: the sum of
`a_{ij,S}` over the double surfaces `S ⊆ Eᵢ ∩ Eⱼ` (`j ≠ i`) whose generic point is the image of
the generic point of `P`, that is, the double surfaces equal to `P`. -/
def surfaceCoefficientCoeff (a : DoubleSurface B → ℚ) (E : Mori.PrimeDivisor Z)
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) : ℚ :=
  ∑ᶠ σ : {σ : DoubleSurface B // σ.fst = E ∧
      σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint}}, a σ

/-- For a fixed component `E` and prime divisor `P` of `E`, the double surfaces
`S ⊆ E ∩ Eⱼ` equal to `P` are determined by `Eⱼ`, hence finitely many. -/
theorem finite_doubleSurfaces_eq (E : Mori.PrimeDivisor Z)
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) :
    Finite {σ : DoubleSurface B // σ.fst = E ∧
      σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint}} := by
  refine Finite.of_injective (β := B.support) (fun σ => ⟨σ.1.snd, σ.1.snd_mem⟩) ?_
  rintro ⟨σ, hσ₁, hσ₂⟩ ⟨τ, hτ₁, hτ₂⟩ h
  exact Subtype.ext (DoubleSurface.ext (hσ₁.trans hτ₁.symm) (congrArg Subtype.val h)
    (hσ₂.trans hτ₂.symm))

/-- On a Noetherian scheme only finitely many prime divisors of `Eᵢ` have nonzero coefficient
in `Zᵢ(a)`. -/
theorem finite_support_surfaceCoefficientCoeff [NoetherianSpace Z] (a : DoubleSurface B → ℚ)
    (E : Mori.PrimeDivisor Z) : (Function.support (surfaceCoefficientCoeff a E)).Finite := by
  classical
  have hfin : {S : Set Z | ∃ σ : DoubleSurface B, σ.fst = E ∧ σ.carrier = S}.Finite := by
    refine (B.support.finite_toSet.biUnion fun E' _ =>
      DoubleSurface.finite_setOf_carrier (B := B) E E').subset ?_
    rintro S ⟨σ, h₁, h₂⟩
    exact Set.mem_biUnion (x := σ.snd) σ.snd_mem ⟨σ, h₁, rfl, h₂⟩
  let ι := E.idealSheaf.subschemeι
  have hinj : Function.Injective
      fun P : Mori.PrimeDivisor E.idealSheaf.subscheme => closure {ι P.genericPoint} := by
    intro P Q h
    have hQ : IsGenericPoint (ι Q.genericPoint) (closure {ι P.genericPoint}) := by
      rw [show closure {ι P.genericPoint} = closure {ι Q.genericPoint} from h]
      exact isGenericPoint_closure
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (ι.isClosedEmbedding.injective (isGenericPoint_closure.eq hQ))
  refine (hfin.preimage hinj.injOn).subset ?_
  intro P hP
  by_contra hnot
  apply hP
  have : IsEmpty {σ : DoubleSurface B // σ.fst = E ∧
      σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint}} :=
    ⟨fun σ => hnot ⟨σ.1, σ.2.1, σ.2.2⟩⟩
  exact finsum_of_isEmpty _

open Classical in
/-- The divisor `Zᵢ(a) = ∑_{j ≠ i} ∑_{S ⊆ Eᵢ ∩ Eⱼ} a_{ij,S} S` of a surface coefficient system
`a` on the component `E = Eᵢ`, a `ℚ`-divisor on the scheme `Eᵢ`. Its coefficient at a prime
divisor `P` of `Eᵢ` is `MMP.Fourfold.surfaceCoefficientCoeff` (on a Noetherian scheme,
`MMP.Fourfold.coeff_surfaceCoefficientDivisor`). -/
@[mmp "def_mmp_conductor_surface_coefficients"]
def surfaceCoefficientDivisor (a : DoubleSurface B → ℚ) (E : Mori.PrimeDivisor Z) :
    QDivisor E.idealSheaf.subscheme :=
  if h : (Function.support (surfaceCoefficientCoeff a E)).Finite then
    Finsupp.ofSupportFinite _ h
  else 0

/-- On a Noetherian scheme the coefficient of `Zᵢ(a)` at a prime divisor `P` of `Eᵢ` is
`MMP.Fourfold.surfaceCoefficientCoeff a E P`. -/
theorem coeff_surfaceCoefficientDivisor [NoetherianSpace Z] (a : DoubleSurface B → ℚ)
    (E : Mori.PrimeDivisor Z) (P : Mori.PrimeDivisor E.idealSheaf.subscheme) :
    (surfaceCoefficientDivisor a E).coeff P = surfaceCoefficientCoeff a E P := by
  rw [surfaceCoefficientDivisor,
    dite_eq_left_of_eq_true (eq_true (finite_support_surfaceCoefficientCoeff a E))]
  rfl

/-! ### The coefficient along a connected subset of a double intersection -/

/-- The double surface of `(Eᵢ, Eⱼ)` containing a nonempty subset `T ⊆ Eᵢ ∩ Eⱼ`: the connected
component of `Eᵢ ∩ Eⱼ` through a point of `T`. For `T` connected it is the unique double surface
of `(Eᵢ, Eⱼ)` containing `T` (`MMP.Fourfold.DoubleSurface.subset_through`,
`MMP.Fourfold.DoubleSurface.eq_through`). -/
def DoubleSurface.through {E E' : Mori.PrimeDivisor Z} (hE : E ∈ B.support) (hE' : E' ∈ B.support)
    (hne : E ≠ E') {T : Set Z} (hT : T.Nonempty) (hTE : T ⊆ E.support ∩ E'.support) :
    DoubleSurface B where
  fst := E
  snd := E'
  fst_mem := hE
  snd_mem := hE'
  fst_ne_snd := hne
  carrier := connectedComponentIn (E.support ∩ E'.support) hT.some
  isComponent := ⟨hT.some, hTE hT.some_mem, rfl⟩

/-- A nonempty connected subset `T ⊆ Eᵢ ∩ Eⱼ` is contained in the double surface through `T`. -/
theorem DoubleSurface.subset_through {E E' : Mori.PrimeDivisor Z} (hE : E ∈ B.support)
    (hE' : E' ∈ B.support) (hne : E ≠ E') {T : Set Z} (hT : T.Nonempty)
    (hTE : T ⊆ E.support ∩ E'.support) (hTc : IsPreconnected T) :
    T ⊆ (DoubleSurface.through hE hE' hne hT hTE).carrier :=
  hTc.subset_connectedComponentIn hT.some_mem hTE

/-- A double surface of `(Eᵢ, Eⱼ)` meeting a connected subset `T` of `Eᵢ ∩ Eⱼ` is the double
surface through `T`. -/
theorem DoubleSurface.eq_through {E E' : Mori.PrimeDivisor Z} (hE : E ∈ B.support)
    (hE' : E' ∈ B.support) (hne : E ≠ E') {T : Set Z} (hT : T.Nonempty)
    (hTE : T ⊆ E.support ∩ E'.support) (hTc : IsPreconnected T) (σ : DoubleSurface B)
    (h₁ : σ.fst = E) (h₂ : σ.snd = E') (hσ : (σ.carrier ∩ T).Nonempty) :
    σ = DoubleSurface.through hE hE' hne hT hTE := by
  obtain ⟨y, hyσ, hyT⟩ := hσ
  refine DoubleSurface.ext h₁ h₂ ?_
  rw [σ.carrier_eq_connectedComponentIn hyσ, h₁, h₂]
  exact (connectedComponentIn_eq (hTc.subset_connectedComponentIn hT.some_mem hTE hyT)).symm

/-- The coefficient `a_{ij,T}` of a surface coefficient system along a nonempty subset
`T ⊆ Eᵢ ∩ Eⱼ`, `i ≠ j`: the coefficient of the double surface through `T`. For `T` a connected
component of a triple intersection `Eᵢ ∩ Eⱼ ∩ Eₖ` it is the coefficient on the unique double
surface of `(Eᵢ, Eⱼ)` containing `T`. -/
@[mmp "def_mmp_conductor_surface_coefficients"]
def coeffAlong (a : DoubleSurface B → ℚ) {E E' : Mori.PrimeDivisor Z} (hE : E ∈ B.support)
    (hE' : E' ∈ B.support) (hne : E ≠ E') {T : Set Z} (hT : T.Nonempty)
    (hTE : T ⊆ E.support ∩ E'.support) : ℚ :=
  a (DoubleSurface.through hE hE' hne hT hTE)

/-- Along a connected subset `T`, `a_{ij,T}` is the coefficient of any double surface of
`(Eᵢ, Eⱼ)` meeting `T`. -/
theorem coeffAlong_eq (a : DoubleSurface B → ℚ) {E E' : Mori.PrimeDivisor Z} (hE : E ∈ B.support)
    (hE' : E' ∈ B.support) (hne : E ≠ E') {T : Set Z} (hT : T.Nonempty)
    (hTE : T ⊆ E.support ∩ E'.support) (hTc : IsPreconnected T) (σ : DoubleSurface B)
    (h₁ : σ.fst = E) (h₂ : σ.snd = E') (hσ : (σ.carrier ∩ T).Nonempty) :
    coeffAlong a hE hE' hne hT hTE = a σ := by
  rw [coeffAlong, DoubleSurface.eq_through hE hE' hne hT hTE hTc σ h₁ h₂ hσ]

/-- For an oriented system, `a_{ji,T} = -a_{ij,T}`. -/
theorem coeffAlong_swap {a : DoubleSurface B → ℚ} (ha : a ∈ orientedSurfaceCoefficients B)
    {E E' : Mori.PrimeDivisor Z} (hE : E ∈ B.support) (hE' : E' ∈ B.support) (hne : E ≠ E')
    {T : Set Z} (hT : T.Nonempty) (hTE : T ⊆ E.support ∩ E'.support) (hTc : IsPreconnected T) :
    coeffAlong a hE' hE hne.symm hT (Set.inter_comm E.support E'.support ▸ hTE) =
      -coeffAlong a hE hE' hne hT hTE := by
  set σ := DoubleSurface.through hE hE' hne hT hTE
  rw [coeffAlong_eq a hE' hE hne.symm hT _ hTc σ.swap rfl rfl
    ⟨hT.some, DoubleSurface.subset_through hE hE' hne hT hTE hTc hT.some_mem, hT.some_mem⟩]
  exact ha σ

end MMP.Fourfold
