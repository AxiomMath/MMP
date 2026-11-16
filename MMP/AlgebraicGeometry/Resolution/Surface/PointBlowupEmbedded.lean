module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Resolution.Surface.CurveMultiplicity
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic

/-!
# Point blow-ups and embedded resolution (Kollár, *Resolution of singularities*, §1.4–1.5)

Let `S` be a Noetherian scheme and `0 ∈ S` a closed point. The *blow-up* `π : B₀S → S` of `0` is
the relative `Proj` of the Rees algebra of the ideal of the reduced point, its *exceptional curve*
`E = π⁻¹(0)`, and the *birational transform* of a closed subscheme `C ⊆ S` is the scheme-theoretic
closure of `π⁻¹(C) ∖ E` in `B₀S` (Kollár 1.36, 1.38). Iterating, a *weak embedded resolution
sequence* (Algorithm 1.42) blows up singular points of the successive birational transforms, a
*strong embedded resolution sequence* (Algorithm 1.46) blows up points where the reduced total
transform does not have simple normal crossings (Definition 1.44). Further: the multiplicity
`mult f` and the leading term of a function in a two-dimensional regular local ring (1.37–1.38),
the infinitely near singularities (1.39), the local intersection number (1.50), the order
function of a DVR (1.22) and the DVR-normalization of a domain (1.23).

## Main definitions

* `MMP.Resolution.localIntersectionNumber`: `(C · D)_P = dim_k 𝒪_{S,P} / (I_{C,P} + I_{D,P})`.
* `MMP.Resolution.dvrNormalization`: the DVR-normalization `S̄^dvr ⊆ Q(S)`.
* `MMP.Resolution.dvrOrder`, `MMP.Resolution.HasZeroOfOrder`, `MMP.Resolution.HasPoleOfOrder`:
  the order `v_R(z) ∈ ℤ ∪ {±∞}` of an element of the fraction field of a DVR.
* `MMP.Resolution.HasSNCAt`, `MMP.Resolution.IsSNCSubscheme`: simple normal crossings at a
  point, and snc divisors.
* `MMP.Resolution.IsRegularSurface`: Noetherian regular schemes with two-dimensional local rings
  at closed points.
* `MMP.Resolution.CoordinateNeighbourhood`: an affine open `Spec R ∋ 0`, `R` a domain, with
  `x, y ∈ R` generating `𝔪₀`.
* `MMP.Resolution.birationalTransform`: the birational transform `C₁ ⊆ B₀S` of `C ⊆ S`.
* `MMP.Resolution.IsCompositeOfPointBlowupsOfLength`, `MMP.Resolution.IsCompositeOfPointBlowups`:
  composites of (`m`) point blow-ups.
* `MMP.Resolution.PointBlowupSequence`: a sequence of point blow-ups of length `n ∈ ℕ ∪ {∞}`,
  with `σᵢ₊₁` and `πᵢ`; `MMP.Resolution.PointBlowupSequence.IsStrongEmbeddedResolution` and
  `MMP.Resolution.PointBlowupSequence.IsWeakEmbeddedResolution` (and `…Stops`) single out the
  strong and weak embedded resolution sequences.
* `MMP.Resolution.idealOrder`, `MMP.Resolution.mult`, `MMP.Resolution.multAt`: `ord(I)`,
  `mult f` and `mult_P C`.
* `MMP.Resolution.infinitelyNearSingularities`: the sets `N_n(0 ∈ C ⊆ S)`.
* `MMP.Resolution.IsLeadingTerm`: leading terms of `f` with respect to `x, y`.

## Implementation notes

Closed subschemes are Mathlib's `Scheme.IdealSheafData`; the inverse image of a closed subscheme
is `Scheme.IdealSheafData.comap`, the reduced closed subscheme on a closed set `Z` is
`Scheme.IdealSheafData.vanishingIdeal Z`, the stalk `I_{C,P} ⊆ 𝒪_{S,P}` is
`AlgebraicGeometry.IdealSheafData.stalk`, and the local ring `𝒪_{C,P}` of a closed subscheme is
`𝒪_{S,P} / I_{C,P}`. The blow-up of a closed point `0` (Kollár 1.36) is StacksDraft's
`AlgebraicGeometry.blowUp` of `vanishingIdeal {0}`, with structure morphism
`AlgebraicGeometry.blowUpToBase`, and its exceptional curve `π⁻¹(0)` is
`AlgebraicGeometry.exceptionalIdeal`; neither is restated here. The exceptional set of
Kollár 1.48 is `MMP.Mori.exceptionalSet`, registered below.

Kollár writes `S_{i+1} = B_{p_i}S_i`; a `PointBlowupSequence` carries an isomorphism
`S_{i+1} ≅ B_{p_i}S_i` (and `S_0 ≅ S₀`) instead, with `σ_{i+1}` the composite with the blow-up
morphism. A sequence of length `n ∈ ℕ∞` has schemes `S_i` and points `p_i` for every `i : ℕ`;
only `S_i` with `i ≤ n` and `p_i` with `i < n` take part in the conditions, the others are junk.
In a weak embedded resolution sequence the subschemes `C_i` are determined by `C₀` (each is the
birational transform of the previous one), so they are computed by
`PointBlowupSequence.transformedSubscheme` rather than carried as data.

The standing hypotheses of the source (Noetherian, regular, `0` closed, `P` isolated in `C ∩ D`,
`x, y` a regular system of parameters) are dropped where the definition makes sense without them.
The DVRs tested in `dvrNormalization` range over the universe of `S`; this gives the same set,
since a DVR `R ⊇ φ(S)` can be replaced by `R ∩ Q(φ(S))`, a DVR of `Q(S)` or `Q(S)` itself.
`IsLeadingTerm` is stated without the map `φ_m`: `φ_m(F)` is the class of `G(x, y)` for any
lift `G ∈ A[X, Y]_m` of `F`, so `F` is a leading term of `f` exactly when
`f - G(x, y) ∈ 𝔪^{m+1}` for some homogeneous lift `G` of degree `m`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace MMP.Resolution

/-! ### The local intersection number -/

section LocalIntersection

variable {k : Type u} [Field k] {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))

/-- The *local intersection number* `(C · D)_P = dim_k 𝒪_{S,P} / (I_{C,P} + I_{D,P}) ∈ ℕ ∪ {∞}`
of closed subschemes `C`, `D` of a scheme `S` over `k` at a point `P` (Kollár 1.50; there `C`,
`D` are effective Cartier divisors and `P` is an isolated closed point of `C ∩ D`). -/
@[mmp "def_kr1b_local_intersection_number"]
noncomputable def localIntersectionNumber (C D : S.IdealSheafData) (P : S) : ℕ∞ :=
  letI := MMP.Mori.stalkAlgebra sS P
  (Module.rank k (S.presheaf.stalk P ⧸
    (IdealSheafData.stalk C P ⊔ IdealSheafData.stalk D P))).toENat

/-- With local equations `f_P`, `g_P` of `C`, `D` at `P`,
`(C · D)_P = dim_k 𝒪_{S,P} / (f_P, g_P)`. -/
theorem localIntersectionNumber_eq_of_stalk_eq_span {C D : S.IdealSheafData} {P : S}
    {f g : S.presheaf.stalk P} (hf : IdealSheafData.stalk C P = Ideal.span {f})
    (hg : IdealSheafData.stalk D P = Ideal.span {g}) :
    localIntersectionNumber sS C D P =
      letI := MMP.Mori.stalkAlgebra sS P
      (Module.rank k (S.presheaf.stalk P ⧸ Ideal.span {f, g})).toENat := by
  unfold localIntersectionNumber
  rw [hf, hg, ← Ideal.span_union, Set.singleton_union]

end LocalIntersection

/-! ### DVR-normalization and the order function of a DVR -/

section DVR

variable (S : Type u) [CommRing S] [IsDomain S]

/-- The *DVR-normalization* `S̄^dvr ⊆ Q(S)` of an integral domain `S` (Kollár Def. 1.23): the
elements `z` with `Φ_φ(z) ∈ R` for every DVR `R` and every injective ring homomorphism
`φ : S → R`, where `Φ_φ : Q(S) → Q(R)` is the induced homomorphism of fraction fields. -/
@[mmp "def_kr1b_dvr_normalization"]
def dvrNormalization : Set (FractionRing S) :=
  {z | ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (φ : S →+* R)
      (hφ : Function.Injective φ),
      IsFractionRing.map (K := FractionRing S) (L := FractionRing R) hφ z ∈
        Set.range (algebraMap R (FractionRing R))}

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The *order* `v_R(z) = sup {n ∈ ℤ : z ∈ tⁿR} ∈ ℤ ∪ {±∞}` of an element `z` of the fraction
field of a DVR `R`, for the chosen generator `t` of the maximal ideal of `R`; `tⁿR ⊆ Q(R)` is
the `R`-submodule generated by `tⁿ`, also for `n < 0` (Kollár 1.22). -/
@[mmp "def_kr1b_dvr_order"]
noncomputable def dvrOrder (z : FractionRing R) : WithTop (WithBot ℤ) :=
  ⨆ (n : ℤ) (_ : ∃ r : R, z = algebraMap R (FractionRing R) r *
      algebraMap R (FractionRing R) (Submodule.IsPrincipal.generator (maximalIdeal R)) ^ n),
    ((n : WithBot ℤ) : WithTop (WithBot ℤ))

/-- `z` has a *zero of order `n`* if `v_R(z) = n > 0` (Kollár 1.22). -/
@[mmp "def_kr1b_dvr_order"]
def HasZeroOfOrder (z : FractionRing R) (n : ℤ) : Prop :=
  0 < n ∧ dvrOrder R z = ((n : WithBot ℤ) : WithTop (WithBot ℤ))

/-- `z` has a *pole of order `n`* if `v_R(z) = -n < 0` (Kollár 1.22). -/
@[mmp "def_kr1b_dvr_order"]
def HasPoleOfOrder (z : FractionRing R) (n : ℤ) : Prop :=
  0 < n ∧ dvrOrder R z = (((-n : ℤ) : WithBot ℤ) : WithTop (WithBot ℤ))

end DVR

/-! ### Simple normal crossings -/

section SNC

variable {X : Scheme.{u}}

/-- A closed subscheme `D ⊆ X` has *simple normal crossings at* `p` (Kollár Def. 1.44, local
form) if there are an open `U ∋ p`, sections `x₁, …, x_d ∈ 𝒪_X(U)` whose germs form a regular
system of parameters of `𝒪_{X,p}` (so `d = dim 𝒪_{X,p}`), and `m₁, …, m_d ∈ ℕ` with
`D ∩ U = V(∏ᵢ xᵢ^{mᵢ})` as closed subschemes of `U`, that is, the stalk of the ideal of `D` at
every `q ∈ U` is generated by the germ of `∏ᵢ xᵢ^{mᵢ}`. -/
@[mmp "def_kr1b_snc_at_point"]
def HasSNCAt (D : X.IdealSheafData) (p : X) : Prop :=
  ∃ (d : ℕ) (U : X.Opens) (hp : p ∈ U) (x : Fin d → Γ(X, U)) (m : Fin d → ℕ),
    MMP.Mori.IsRegularSystemOfParameters (fun i => (X.presheaf.germ U p hp).hom (x i)) ∧
      ∀ (q : X) (hq : q ∈ U), IdealSheafData.stalk D q =
        Ideal.span {(X.presheaf.germ U q hq).hom (∏ i, x i ^ m i)}

/-- A closed subscheme `D ⊆ X` is a *simple normal crossing divisor* if it has simple normal
crossings at every closed point of `X` (Kollár Def. 1.44). -/
@[mmp "def_kr1b_snc_divisor"]
def IsSNCSubscheme (D : X.IdealSheafData) : Prop :=
  ∀ p : X, IsClosed ({p} : Set X) → HasSNCAt D p

end SNC

/-! ### Regular surfaces and coordinate neighbourhoods -/

/-- A *regular surface* is a Noetherian regular scheme `S` with `dim 𝒪_{S,p} = 2` for every
closed point `p ∈ S`. -/
@[mmp "def_kr1b_regular_surface"]
def IsRegularSurface (S : Scheme.{u}) : Prop :=
  IsNoetherian S ∧ (∀ p : S, IsRegularLocalRing (S.presheaf.stalk p)) ∧
    ∀ p : S, IsClosed ({p} : Set S) → ringKrullDim (S.presheaf.stalk p) = 2

/-- A *coordinate neighbourhood* of a point `0 ∈ S` (Kollár 1.36): an affine open
`U = Spec R ∋ 0` of `S` with `R` an integral domain, and `x, y ∈ R` with `(x, y)R = 𝔪₀`, the
(maximal) ideal of `R` of the point `0`. -/
@[mmp "def_kr1b_coordinate_neighbourhood"]
structure CoordinateNeighbourhood (S : Scheme.{u}) (p : S) where
  /-- The affine open `U = Spec R`. -/
  U : S.Opens
  isAffineOpen : IsAffineOpen U
  mem : p ∈ U
  isDomain : IsDomain Γ(S, U)
  /-- The first coordinate. -/
  x : Γ(S, U)
  /-- The second coordinate. -/
  y : Γ(S, U)
  span_eq : Ideal.span {x, y} = (isAffineOpen.primeIdealOf ⟨p, mem⟩).asIdeal

/-! ### The exceptional set -/

attribute [mmp "def_kr1b_exceptional_set"] MMP.Mori.exceptionalSet

/-! ### The birational transform -/

section BirationalTransform

variable {S : Scheme.{u}}

/-- The *birational transform* `C₁ ⊆ B₀S` of a closed subscheme `C ⊆ S` in the blow-up of a
closed point `0` (Kollár 1.38): the scheme-theoretic closure in `B₀S` of the open subscheme
`π⁻¹(C) ∖ E` of `π⁻¹(C) = C ×_S B₀S`, `E` the exceptional curve. -/
@[mmp "def_kr1b_birational_transform_curve"]
noncomputable def birationalTransform (p : S) (hp : IsClosed ({p} : Set S))
    (C : S.IdealSheafData) :
    (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).IdealSheafData :=
  (((Limits.pullback.snd C.subschemeι
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))) ⁻¹ᵁ
        (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support.compl).ι ≫
    Limits.pullback.snd C.subschemeι
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))).ker

end BirationalTransform

/-! ### Composites of point blow-ups -/

/-- `g : S' → S` is a *composite of `m` point blow-ups* (Kollár 1.48): for `m = 0`, `g` is an
isomorphism; for `m + 1`, `g = φ ∘ σ ∘ h` (written diagrammatically below) where `h : W → S` is a
composite of `m` point blow-ups, `σ : B_wW → W` is the blow-up of a closed point `w ∈ W` and
`φ : S' ≅ B_wW` is an isomorphism. -/
@[mmp "def_kr1b_composite_of_point_blowups"]
def IsCompositeOfPointBlowupsOfLength : ℕ → ∀ {S' S : Scheme.{u}}, (S' ⟶ S) → Prop
  | 0, _, _, g => IsIso g
  | m + 1, S', S, g => ∃ (W : Scheme.{u}) (h : W ⟶ S) (w : W) (hw : IsClosed ({w} : Set W)),
      IsCompositeOfPointBlowupsOfLength m h ∧
        ∃ φ : S' ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩),
          g = φ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h

/-- `g` is a *composite of point blow-ups* if it is a composite of `m` point blow-ups for some
`m` (Kollár 1.48). -/
@[mmp "def_kr1b_composite_of_point_blowups"]
def IsCompositeOfPointBlowups {S' S : Scheme.{u}} (g : S' ⟶ S) : Prop :=
  ∃ m : ℕ, IsCompositeOfPointBlowupsOfLength m g

/-! ### Sequences of point blow-ups and embedded resolution -/

/-- A sequence of point blow-ups of `S₀` of length `n ∈ ℕ ∪ {∞}`: schemes `S_i` with
`S_0 ≅ S₀`, closed points `p_i ∈ S_i` and isomorphisms `S_{i+1} ≅ B_{p_i}S_i` for `i < n`.
The `S_i` with `i > n` and the `p_i` with `i ≥ n` are junk. -/
@[mmp "def_kr1b_strong_embedded_resolution_sequence",
  mmp "def_kr1b_weak_embedded_resolution_sequence"]
structure PointBlowupSequence (S₀ : Scheme.{u}) where
  /-- The length `n ∈ ℕ ∪ {∞}`. -/
  length : ℕ∞
  /-- The schemes `S_i`. -/
  S : ℕ → Scheme.{u}
  /-- The identification `S_0 ≅ S₀`. -/
  zeroIso : S 0 ≅ S₀
  /-- The centres `p_i ∈ S_i`. -/
  p : ∀ i : ℕ, S i
  isClosed_p : ∀ i : ℕ, (i : ℕ∞) < length → IsClosed ({p i} : Set (S i))
  /-- The identification `S_{i+1} ≅ B_{p_i}S_i`. -/
  blowupIso : ∀ (i : ℕ) (hi : (i : ℕ∞) < length),
    S (i + 1) ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p i}, isClosed_p i hi⟩)

namespace PointBlowupSequence

variable {S₀ : Scheme.{u}} (s : PointBlowupSequence S₀)

/-- The blow-up morphism `σ_{i+1} : S_{i+1} = B_{p_i}S_i → S_i`. -/
noncomputable def σ (i : ℕ) (hi : (i : ℕ∞) < s.length) : s.S (i + 1) ⟶ s.S i :=
  (s.blowupIso i hi).hom ≫
    blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{s.p i}, s.isClosed_p i hi⟩)

/-- If `i + 1 ≤ n` in `ℕ∞`, then `i < n`. -/
theorem coe_lt_of_succ_le {i : ℕ} {n : ℕ∞} (h : ((i + 1 : ℕ) : ℕ∞) ≤ n) : (i : ℕ∞) < n :=
  lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self i)) h

/-- The composite `π_i = σ_1 ∘ ⋯ ∘ σ_i : S_i → S_0 ≅ S₀`, for `i ≤ n`. -/
noncomputable def π : ∀ i : ℕ, (i : ℕ∞) ≤ s.length → (s.S i ⟶ S₀)
  | 0, _ => s.zeroIso.hom
  | i + 1, h => s.σ i (coe_lt_of_succ_le h) ≫ π i (coe_lt_of_succ_le h).le

/-- The sequence is a *strong embedded resolution sequence* for `(S₀, C₀)` (Kollár
Algorithm 1.46): for every `i < n`, `p_i ∈ π_i⁻¹(C₀)` and the reduced closed subscheme
`π_i⁻¹(C₀)_red` does not have simple normal crossings at `p_i`. -/
@[mmp "def_kr1b_strong_embedded_resolution_sequence"]
def IsStrongEmbeddedResolution (C₀ : S₀.IdealSheafData) : Prop :=
  ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length),
    s.p i ∈ (C₀.comap (s.π i hi.le)).support ∧
      ¬ HasSNCAt (Scheme.IdealSheafData.vanishingIdeal (C₀.comap (s.π i hi.le)).support) (s.p i)

/-- A strong embedded resolution sequence *stops* if it has finite length `n` and
`π_n⁻¹(C₀)_red` is an snc divisor (Kollár Algorithm 1.46). -/
@[mmp "def_kr1b_strong_embedded_resolution_sequence"]
def StrongEmbeddedResolutionStops (C₀ : S₀.IdealSheafData) : Prop :=
  ∃ (n : ℕ) (hn : s.length = n),
    IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal (C₀.comap (s.π n hn.ge)).support)

open Classical in
/-- The successive birational transforms `C_i ⊆ S_i` of `C₀ ⊆ S₀`: `C_0` is `C₀` on `S_0 ≅ S₀`
and `C_{i+1} ⊆ S_{i+1} = B_{p_i}S_i` is the birational transform of `C_i`, for `i < n`
(junk `⊤`, the empty subscheme, beyond). -/
@[mmp "def_kr1b_weak_embedded_resolution_sequence"]
noncomputable def transformedSubscheme (C₀ : S₀.IdealSheafData) :
    ∀ i : ℕ, (s.S i).IdealSheafData
  | 0 => C₀.comap s.zeroIso.hom
  | i + 1 =>
    if hi : (i : ℕ∞) < s.length then
      (birationalTransform (s.p i) (s.isClosed_p i hi) (transformedSubscheme C₀ i)).comap
        (s.blowupIso i hi).hom
    else ⊤

/-- The sequence is a *weak embedded resolution sequence* for `(S₀, C₀)` (Kollár
Algorithm 1.42): for every `i < n`, `p_i` is a point of `C_i` (the `i`-th birational transform of
`C₀`) at which `𝒪_{C_i,p_i} = 𝒪_{S_i,p_i} / I_{C_i,p_i}` is not a regular local ring. -/
@[mmp "def_kr1b_weak_embedded_resolution_sequence"]
def IsWeakEmbeddedResolution (C₀ : S₀.IdealSheafData) : Prop :=
  ∀ (i : ℕ) (_ : (i : ℕ∞) < s.length),
    s.p i ∈ (s.transformedSubscheme C₀ i).support ∧
      ¬ IsRegularLocalRing ((s.S i).presheaf.stalk (s.p i) ⧸
        IdealSheafData.stalk (s.transformedSubscheme C₀ i) (s.p i))

/-- A weak embedded resolution sequence *stops* if it has finite length `n` and `𝒪_{C_n,p}` is
regular for every closed point `p ∈ C_n` (Kollár Algorithm 1.42). -/
@[mmp "def_kr1b_weak_embedded_resolution_sequence"]
def WeakEmbeddedResolutionStops (C₀ : S₀.IdealSheafData) : Prop :=
  ∃ n : ℕ, s.length = n ∧
    ∀ q : s.S n, IsClosed ({q} : Set (s.S n)) → q ∈ (s.transformedSubscheme C₀ n).support →
      IsRegularLocalRing ((s.S n).presheaf.stalk q ⧸
        IdealSheafData.stalk (s.transformedSubscheme C₀ n) q)

end PointBlowupSequence

/-! ### Order and multiplicity -/

section Order

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The *order* `ord(I) = sup {j ≥ 0 : I ⊆ 𝔪ʲ} ∈ ℕ ∪ {∞}` of an ideal `I` of a local ring
`(R, 𝔪)`, with `𝔪⁰ = R` (Kollár §1.5). -/
@[mmp "def_kr1b_order_of_function"]
noncomputable def idealOrder (I : Ideal R) : ℕ∞ :=
  ⨆ (j : ℕ) (_ : I ≤ maximalIdeal R ^ j), (j : ℕ∞)

/-- The *multiplicity* `mult f = ord(fR)` of an element `f` of a local ring (Kollár §1.5). -/
@[mmp "def_kr1b_order_of_function"]
noncomputable def mult (f : R) : ℕ∞ :=
  idealOrder (Ideal.span {f})

/-- The *multiplicity* `mult_P C = ord(I_{C,P})` of a closed subscheme `C ⊆ S` at a point `P`,
computed in `𝒪_{S,P}` (Kollár 1.38). -/
@[mmp "def_kr1b_order_of_function"]
noncomputable def multAt {S : Scheme.{u}} (C : S.IdealSheafData) (P : S) : ℕ∞ :=
  idealOrder (IdealSheafData.stalk C P)

end Order

/-! ### Infinitely near singularities -/

/-- A scheme `S` with a closed subscheme `C ⊆ S` and a point `q ∈ S`: the triples `(S, C, q)` of
Kollár Def. 1.39. -/
@[mmp "def_kr1b_infinitely_near_singularity"]
structure PointedSubscheme where
  /-- The ambient scheme. -/
  S : Scheme.{u}
  /-- The closed subscheme. -/
  C : S.IdealSheafData
  /-- The point. -/
  q : S

open Classical in
/-- The set `N_1(0 ∈ C ⊆ S)` of triples `(B₀S, C₁, q)`, `C₁` the birational transform of `C` and
`q` a closed point of `C₁ ∩ E` at which `𝒪_{C₁,q}` is not a regular local ring (Kollár
Def. 1.39); empty if `0` is not a closed point. -/
@[mmp "def_kr1b_infinitely_near_singularity"]
noncomputable def firstInfinitelyNearSingularities (t : PointedSubscheme.{u}) :
    Set PointedSubscheme.{u} :=
  if h : IsClosed ({t.q} : Set t.S) then
    {t' | ∃ q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, h⟩),
      IsClosed ({q} : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, h⟩))) ∧
      q ∈ (birationalTransform t.q h t.C).support ∧
      q ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, h⟩)).support ∧
      ¬ IsRegularLocalRing
        ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, h⟩)).presheaf.stalk q ⧸
          IdealSheafData.stalk (birationalTransform t.q h t.C) q) ∧
      t' = ⟨_, birationalTransform t.q h t.C, q⟩}
  else ∅

/-- The sets `N_n(0 ∈ C ⊆ S)` of *infinitely near singularities in the `n`-th infinitesimal
neighbourhood* of `0 ∈ C` (Kollár Def. 1.39): `N_{n+1} = ⋃_{(S',C',q) ∈ N_n} N_1(q ∈ C' ⊆ S')`.
The index `0` gives `{(S, C, 0)}`, so that `N_1` is `firstInfinitelyNearSingularities`. -/
@[mmp "def_kr1b_infinitely_near_singularity"]
noncomputable def infinitelyNearSingularities (t : PointedSubscheme.{u}) :
    ℕ → Set PointedSubscheme.{u}
  | 0 => {t}
  | n + 1 => ⋃ t' ∈ infinitelyNearSingularities t n, firstInfinitelyNearSingularities t'

/-! ### Leading terms -/

section LeadingTerm

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- A form `F ∈ κ[X, Y]_m` is a *leading term* of `f ∈ A` with respect to `x, y` (Kollár 1.38,
for `(A, 𝔪, κ)` regular local of dimension 2 with regular system of parameters `x, y`), where
`m = mult f < ∞`, if `φ_m(F)` is the class of `f` in `𝔪^m / 𝔪^{m+1}`, `φ_m(X^iY^j)` the class of
`x^iy^j`. Equivalently: some homogeneous `G ∈ A[X, Y]` of degree `m` lifting `F` has
`f - G(x, y) ∈ 𝔪^{m+1}`. -/
@[mmp "def_kr1b_leading_term"]
def IsLeadingTerm (x y f : A) (F : MvPolynomial (Fin 2) (ResidueField A)) : Prop :=
  ∃ m : ℕ, mult f = m ∧ F.IsHomogeneous m ∧
    ∃ G : MvPolynomial (Fin 2) A, G.IsHomogeneous m ∧ MvPolynomial.map (residue A) G = F ∧
      f - MvPolynomial.eval ![x, y] G ∈ maximalIdeal A ^ (m + 1)

end LeadingTerm

end MMP.Resolution
