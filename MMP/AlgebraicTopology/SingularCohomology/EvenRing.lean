module

public import MMP.AlgebraicTopology.SingularCohomology.Unit
public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Commutative
public import MMP.AlgebraicTopology.OrientationClass.CupCompositeNaturality

/-!
# The even cohomology ring `H^{ev} Y = ⨁_p H^{2p}(Y; R)` (Fulton, §19.1)

For a topological space `Y` and a commutative ring `R`, the cup product
`H^{2p} Y × H^{2q} Y → H^{2(p+q)} Y` of singular cohomology, with unit `1 ∈ H^0 Y`, makes the
even-degree cohomology `⨁_{p ≥ 0} H^{2p}(Y; R)` a commutative, associative, `ℤ_{≥0}`-graded ring
(the grading `p` is half the cohomological degree). This is the ring `H^* X` of Fulton,
Corollary 19.2(b), in which the cycle map `cl : A^* X → H^* X` takes values.

*Proof.* On absolute classes the cup product `[φ] ∪ [ψ] = [ρ^* (φ ∪ ψ)]` is the class of the
Alexander–Whitney cup `φ ∪ ψ` itself, because `ρ^* χ - χ` is a coboundary for every cocycle `χ`
(`MMP.SingularCochain.pullback_smallChainMap_sub_mem_relCoboundaries`). The
Alexander–Whitney cup is strictly associative and has the constant `0`-cochain `1` as two-sided
unit at the level of cochains; the cup product is graded commutative with sign
`(-1)^{2p · 2q} = 1` (`MMP.cohomologyWithSupports.cup_comm`).

## Main definitions

* `MMP.cupUniv`: the cup product `H^{2p} Y × H^{2q} Y → H^{2(p+q)} Y`.
* `MMP.EvenCohomologyRing R Y`: `⨁_p H^{2p}(Y; R)`.
* `MMP.EvenCohomologyRing.gCommRing`: the family `p ↦ H^{2p}(Y; R)` is a graded
  commutative ring under `cupUniv`, with unit `1 ∈ H^0 Y`; through `DirectSum.commRing` it makes
  `EvenCohomologyRing R Y` a commutative ring.

## Main results

* `MMP.cupUniv_ofCocycle`: on classes of cocycles `cupUniv` is the class of the
  Alexander–Whitney cup product.
* `MMP.EvenCohomologyRing.gradedMonoid_mk_cupUniv_assoc`,
  `MMP.EvenCohomologyRing.gradedMonoid_mk_cupUniv_comm`,
  `MMP.EvenCohomologyRing.gradedMonoid_mk_oneEven_cupUniv`,
  `MMP.EvenCohomologyRing.gradedMonoid_mk_cupUniv_oneEven`: associativity,
  commutativity and the unit laws on homogeneous classes.
* `MMP.EvenCohomologyRing.one_def`,
  `MMP.EvenCohomologyRing.of_mul_of`: the unit is `1 ∈ H^0 Y` and the product of
  homogeneous classes is their cup product.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VII.8.
-/

@[expose] public noncomputable section

open CategoryTheory Set DirectSum

universe u

namespace MMP

open MMP

open SingularChain SingularCochain PoincareAlexander

namespace SingularCochain

open MMP.SingularCochain

variable {R : Type*} [CommRing R] {Y : Type*} [TopologicalSpace Y]

/-- The Alexander–Whitney cup product of cochains is associative. -/
lemma cup_cup_assoc {a b c m k N : ℕ} (hm : a + b = m) (hk : b + c = k) (h₁ : m + c = N)
    (h₂ : a + k = N) (φ : Simplex Y a → R) (ψ : Simplex Y b → R) (χ : Simplex Y c → R) :
    cup m c N h₁ (cup a b m hm φ ψ) χ = cup a k N h₂ φ (cup b c k hk ψ χ) := by
  ext σ
  simp only [cup_apply, comp_smap_comp]
  have e1 : front m N (by omega) ∘ front a m (by omega) = front a N (by omega) := by
    funext j; apply Fin.ext; simp [front_val]
  have e2 : front m N (by omega) ∘ back b m a (by omega) =
      back k N a (by omega) ∘ front b k (by omega) := by
    funext j; apply Fin.ext; simp [front_val, back_val]
  have e3 : back c N m (by omega) = back k N a (by omega) ∘ back c k b (by omega) := by
    funext j; apply Fin.ext; simp only [Function.comp_apply, back_val]; omega
  rw [e1, e2, e3, mul_assoc]

/-- The constant `0`-cochain `1` is a left unit for the cup product. -/
lemma cup_constCochain_one_left {Z : TopCat.{u}} {R : Type u} [CommRing R] (a b : ℕ)
    (h : a + b = b) (φ : Simplex Z b → R) : cup a b b h (constCochain a 1) φ = φ := by
  ext σ
  rw [cup_apply]
  have e : back b b a (by omega) = id := by
    funext j; apply Fin.ext; simp only [back_val, id]; omega
  rw [e, comp_smap_id]
  exact one_mul _

/-- The constant `0`-cochain `1` is a right unit for the cup product. -/
lemma cup_constCochain_one_right {Z : TopCat.{u}} {R : Type u} [CommRing R] (a b : ℕ)
    (h : a + b = a) (φ : Simplex Z a → R) : cup a b a h φ (constCochain b 1) = φ := by
  ext σ
  rw [cup_apply]
  have e : front a a (by omega) = id := by
    funext j; apply Fin.ext; simp only [front_val, id]
  rw [e, comp_smap_id]
  exact mul_one _

/-- The cup product of two absolute cocycles is an absolute cocycle. -/
lemma cup_mem_relCocycles_compl_univ {Z : TopCat.{u}} {R : Type u} [CommRing R] {a b n : ℕ}
    (h : a + b = n) {φ : Simplex Z a → R} (hφ : φ ∈ relCocycles R (univᶜ : Set Z) a)
    {ψ : Simplex Z b → R} (hψ : ψ ∈ relCocycles R (univᶜ : Set Z) b) :
    cup a b n h φ ψ ∈ relCocycles R (univᶜ : Set Z) n := by
  refine ⟨by rw [compl_univ]; exact mem_vanishing_empty _, ?_⟩
  have h1 : coboundary R a φ = 0 := hφ.2
  have h2 : coboundary R b ψ = 0 := hψ.2
  change coboundary R n (cup a b n h φ ψ) = 0
  rw [coboundary_cup, h1, h2]
  simp

end SingularCochain

variable (R : Type u) [CommRing R]

namespace cohomologyWithSupports

/-- The class in `H^n Y` of an absolute `n`-cocycle `φ`. -/
def ofCocycle (Y : TopCat.{u}) (n : ℕ) (φ : Simplex Y n → R)
    (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) n) :
    cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ n :=
  (relativeSingularCohomologyEquiv R (Set.univᶜ : Set Y) n).symm (Submodule.Quotient.mk ⟨φ, hφ⟩)

variable {R}

/-- Equal cocycles have equal classes. -/
lemma ofCocycle_congr {Y : TopCat.{u}} {n : ℕ} {φ φ' : Simplex Y n → R} (h : φ = φ')
    (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) n)
    (hφ' : φ' ∈ relCocycles R (Set.univᶜ : Set Y) n) :
    ofCocycle R Y n φ hφ = ofCocycle R Y n φ' hφ' := by
  subst h; rfl

/-- Every class of `H^n Y` is the class of a cocycle. -/
lemma exists_ofCocycle_eq {Y : TopCat.{u}} (n : ℕ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ n) :
    ∃ (φ : Simplex Y n → R) (hφ : φ ∈ relCocycles R (Set.univᶜ : Set Y) n),
      ofCocycle R Y n φ hφ = x := by
  obtain ⟨⟨φ, hφ⟩, h⟩ :=
    Submodule.Quotient.mk_surjective _ (relativeSingularCohomologyEquiv R (Set.univᶜ : Set Y) n x)
  exact ⟨φ, hφ, by rw [ofCocycle, h, LinearEquiv.symm_apply_apply]⟩

/-- Transport of the class of a relative cocycle along an equality of subsets, for any proof
of the (trivial) equality of degrees. -/
lemma congrIndex_symm_mk' {Y : TopCat.{u}} {S S' : Set Y} (hS : S = S') {n : ℕ}
    (hk : ((n : ℕ) : ℤ) = ((n : ℕ) : ℤ))
    (x : relCocycles R S n) (y : relCocycles R S' n) (hxy : (x : Simplex Y n → R) = y) :
    cohomologyWithSupports.congrIndex R Y hS hk
        ((relativeSingularCohomologyEquiv R S n).symm (Submodule.Quotient.mk x)) =
      (relativeSingularCohomologyEquiv R S' n).symm (Submodule.Quotient.mk y) := by
  subst hS
  obtain rfl := Subtype.ext hxy
  rfl

end cohomologyWithSupports

open MMP.cohomologyWithSupports (ofCocycle ofCocycle_congr exists_ofCocycle_eq congrIndex_symm_mk')

variable {R}

variable (R) in
/-- The cup product `H^{2p} Y × H^{2q} Y → H^{2(p+q)} Y` of absolute cohomology classes. -/
def cupUniv (Y : TopCat.{u}) (p q : ℕ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ) →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * q : ℕ) →ₗ[R]
        cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * (p + q) : ℕ) :=
  (cohomologyWithSupports.cup R Y isClosed_univ isClosed_univ (2 * p : ℕ) (2 * q : ℕ)).compr₂
    (cohomologyWithSupports.congrIndex R Y (by rw [Set.univ_inter])
      (by push_cast; ring)).toLinearMap

/-- On classes of cocycles, `cupUniv` is the class of the Alexander–Whitney cup product. -/
lemma cupUniv_ofCocycle (Y : TopCat.{u}) (p q : ℕ) {φ : Simplex Y (2 * p) → R}
    (hφ : φ ∈ relCocycles R (univᶜ : Set Y) (2 * p)) {ψ : Simplex Y (2 * q) → R}
    (hψ : ψ ∈ relCocycles R (univᶜ : Set Y) (2 * q)) (h : 2 * p + 2 * q = 2 * (p + q)) :
    cupUniv R Y p q (ofCocycle R Y (2 * p) φ hφ) (ofCocycle R Y (2 * q) ψ hψ) =
      ofCocycle R Y (2 * (p + q)) (cup (2 * p) (2 * q) (2 * (p + q)) h φ ψ)
        (cup_mem_relCocycles_compl_univ h hφ hψ) := by
  rw [cupUniv, LinearMap.compr₂_apply, LinearEquiv.coe_coe,
    cohomologyWithSupports.cup_natCast_eq R Y isClosed_univ isClosed_univ (2 * p) (2 * q)
      (2 * (p + q)) h, cohomologyWithSupports.congrIndex_congrIndex, ofCocycle, ofCocycle,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, relCup_mk]
  refine (congrIndex_symm_mk' (S' := (univᶜ : Set Y)) (by rw [union_self]) _
    (relCupCocycles (R := R) isClosed_univ.isOpen_compl isClosed_univ.isOpen_compl (2 * p)
      (2 * q) (2 * (p + q)) h ⟨φ, hφ⟩ ⟨ψ, hψ⟩)
    ⟨(relCupCocycles (R := R) isClosed_univ.isOpen_compl isClosed_univ.isOpen_compl (2 * p)
      (2 * q) (2 * (p + q)) h ⟨φ, hφ⟩ ⟨ψ, hψ⟩ : Simplex Y (2 * (p + q)) → R), by
        refine ⟨fun σ hσ ↦ mem_vanishing_empty (Z := Y) _ σ (by rwa [compl_univ] at hσ), ?_⟩
        exact (relCupCocycles (R := R) isClosed_univ.isOpen_compl isClosed_univ.isOpen_compl
          (2 * p) (2 * q) (2 * (p + q)) h ⟨φ, hφ⟩ ⟨ψ, hψ⟩).2.2⟩ rfl).trans ?_
  rw [ofCocycle]
  congr 1
  rw [Submodule.Quotient.eq]
  exact pullback_smallChainMap_sub_mem_relCoboundaries _
    (cup_mem_relCocycles_compl_univ h hφ hψ)

namespace EvenCohomologyRing

variable (Y : TopCat.{u})

variable (R) in
/-- The unit `1 ∈ H^0 Y`, in the degree `2 * 0` of the even cohomology ring. -/
def oneEven : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * 0 : ℕ) :=
  cohomologyWithSupports.congrIndex R _ rfl (by simp) (cohomologyWithSupports.one R Y)

/-- The unit `oneEven R Y` is the class of the constant `0`-cochain `1`. -/
lemma oneEven_eq_ofCocycle :
    oneEven R Y = ofCocycle R Y (2 * 0) (constCochain (2 * 0) 1)
      (cohomologyWithSupports.constCochain_one_mem_relCocycles_compl_univ Y) :=
  rfl

variable {Y}

/-- Transport of a class of a cup product along an equality of degrees. -/
lemma gradedMonoid_mk_ofCocycle_cup {a b n n' : ℕ} (hnn' : n = n') (hn : a + b = 2 * n)
    (hn' : a + b = 2 * n') {φ : Simplex Y a → R} {ψ : Simplex Y b → R}
    (hc : cup a b (2 * n) hn φ ψ ∈ relCocycles R (univᶜ : Set Y) (2 * n))
    (hc' : cup a b (2 * n') hn' φ ψ ∈ relCocycles R (univᶜ : Set Y) (2 * n')) :
    (GradedMonoid.mk n (ofCocycle R Y (2 * n) _ hc) :
      GradedMonoid fun p : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)) =
      GradedMonoid.mk n' (ofCocycle R Y (2 * n') _ hc') := by
  subst hnn'; rfl

/-- Transport of a transported class along an equality of degrees. -/
lemma gradedMonoid_mk_congrIndex {S : Set Y} {k : ℤ} {n n' : ℕ} (hnn' : n = n')
    (hS : S = (univᶜ : Set Y)) (hk : k = ((2 * n : ℕ) : ℤ)) (hk' : k = ((2 * n' : ℕ) : ℤ))
    (z : relativeSingularCohomology R (ModuleCat.of R R) Y S k) :
    (GradedMonoid.mk n (cohomologyWithSupports.congrIndex R Y hS hk z) :
      GradedMonoid fun p : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)) =
      GradedMonoid.mk n' (cohomologyWithSupports.congrIndex R Y hS hk' z) := by
  subst hnn'; rfl

/-- The cup product of homogeneous classes is associative. -/
theorem gradedMonoid_mk_cupUniv_assoc {p q r : ℕ}
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ))
    (y : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * q : ℕ))
    (z : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * r : ℕ)) :
    (GradedMonoid.mk (p + q + r) (cupUniv R Y (p + q) r (cupUniv R Y p q x y) z) :
      GradedMonoid fun p : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)) =
      GradedMonoid.mk (p + (q + r)) (cupUniv R Y p (q + r) x (cupUniv R Y q r y z)) := by
  obtain ⟨φ, hφ, rfl⟩ := exists_ofCocycle_eq (2 * p) x
  obtain ⟨ψ, hψ, rfl⟩ := exists_ofCocycle_eq (2 * q) y
  obtain ⟨χ, hχ, rfl⟩ := exists_ofCocycle_eq (2 * r) z
  rw [cupUniv_ofCocycle Y p q hφ hψ (by ring), cupUniv_ofCocycle Y (p + q) r _ hχ (by ring),
    cupUniv_ofCocycle Y q r hψ hχ (by ring), cupUniv_ofCocycle Y p (q + r) hφ _ (by ring)]
  rw [gradedMonoid_mk_ofCocycle_cup (add_assoc p q r) (by ring) (by ring) _
    (cup_mem_relCocycles_compl_univ (by ring) (cup_mem_relCocycles_compl_univ (by ring) hφ hψ)
      hχ)]
  congr 1
  exact ofCocycle_congr (cup_cup_assoc _ _ _ _ φ ψ χ) _ _

/-- The cup product of homogeneous classes of even degree is commutative. -/
theorem gradedMonoid_mk_cupUniv_comm {p q : ℕ}
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ))
    (y : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * q : ℕ)) :
    (GradedMonoid.mk (p + q) (cupUniv R Y p q x y) :
      GradedMonoid fun p : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)) =
      GradedMonoid.mk (q + p) (cupUniv R Y q p y x) := by
  have hc := cohomologyWithSupports.cup_comm R Y isClosed_univ isClosed_univ
    ((2 * p : ℕ) : ℤ) ((2 * q : ℕ) : ℤ) x y
  have hs : (((-1 : Rˣ) ^ (((2 * p : ℕ) : ℤ) * ((2 * q : ℕ) : ℤ)) : Rˣ) : R) = 1 := by
    rw [Even.neg_one_zpow ⟨(p : ℤ) * (2 * q), by push_cast; ring⟩, Units.val_one]
  rw [hs, one_smul] at hc
  simp only [cupUniv, LinearMap.compr₂_apply, LinearEquiv.coe_coe]
  rw [← hc, cohomologyWithSupports.congrIndex_congrIndex]
  exact gradedMonoid_mk_congrIndex (add_comm p q) _ _ _ _

/-- The unit `1 ∈ H^0 Y` is a left unit for the cup product. -/
theorem gradedMonoid_mk_oneEven_cupUniv {p : ℕ}
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)) :
    (GradedMonoid.mk (0 + p) (cupUniv R Y 0 p (oneEven R Y) x) :
      GradedMonoid fun p : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)) =
      GradedMonoid.mk p x := by
  obtain ⟨φ, hφ, rfl⟩ := exists_ofCocycle_eq (2 * p) x
  rw [oneEven_eq_ofCocycle, cupUniv_ofCocycle Y 0 p _ hφ (by ring),
    gradedMonoid_mk_ofCocycle_cup (zero_add p) (by ring) (by ring) _
      (cup_mem_relCocycles_compl_univ (by ring)
        (cohomologyWithSupports.constCochain_one_mem_relCocycles_compl_univ Y) hφ)]
  congr 1
  exact ofCocycle_congr (cup_constCochain_one_left _ _ _ φ) _ _

/-- The unit `1 ∈ H^0 Y` is a right unit for the cup product. -/
theorem gradedMonoid_mk_cupUniv_oneEven {p : ℕ}
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)) :
    (GradedMonoid.mk (p + 0) (cupUniv R Y p 0 x (oneEven R Y)) :
      GradedMonoid fun p : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)) =
      GradedMonoid.mk p x := by
  obtain ⟨φ, hφ, rfl⟩ := exists_ofCocycle_eq (2 * p) x
  rw [oneEven_eq_ofCocycle, cupUniv_ofCocycle Y p 0 hφ _ (by ring),
    gradedMonoid_mk_ofCocycle_cup (add_zero p) (by ring) (by ring) _
      (cup_mem_relCocycles_compl_univ (by ring) hφ
        (cohomologyWithSupports.constCochain_one_mem_relCocycles_compl_univ Y))]
  congr 1
  exact ofCocycle_congr (cup_constCochain_one_right _ _ _ φ) _ _

end EvenCohomologyRing

variable (R) in
/-- The even cohomology ring `H^{ev} Y = ⨁_p H^{2p}(Y; R)`, graded by half the degree; its ring
structure is the cup product (`MMP.EvenCohomologyRing.gCommRing`). -/
abbrev EvenCohomologyRing (Y : TopCat.{u}) : Type u :=
  ⨁ p : ℕ, cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)

namespace EvenCohomologyRing

variable (R) (Y : TopCat.{u})

/-- The graded unit `1 ∈ H^0 Y`. -/
instance gOne :
    GradedMonoid.GOne fun p : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ
      (2 * p : ℕ) where
  one := oneEven R Y

/-- The graded product is the cup product, biadditively. -/
instance gNonUnitalNonAssocSemiring :
    GNonUnitalNonAssocSemiring fun p : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ
      (2 * p : ℕ) where
  mul x y := cupUniv R Y _ _ x y
  mul_zero x := map_zero _
  zero_mul y := by simp
  mul_add x y z := map_add _ _ _
  add_mul x y z := by simp

/-- The family `p ↦ H^{2p}(Y; R)` with the cup product and the unit `1 ∈ H^0 Y` is a graded
commutative ring; by `DirectSum.commRing` this makes `EvenCohomologyRing R Y` a commutative
ring. -/
instance gCommRing :
    GCommRing fun p : ℕ ↦ cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ) where
  __ := gNonUnitalNonAssocSemiring R Y
  __ := gOne R Y
  one_mul := fun ⟨_, x⟩ ↦ gradedMonoid_mk_oneEven_cupUniv x
  mul_one := fun ⟨_, x⟩ ↦ gradedMonoid_mk_cupUniv_oneEven x
  mul_assoc := fun ⟨_, x⟩ ⟨_, y⟩ ⟨_, z⟩ ↦ gradedMonoid_mk_cupUniv_assoc x y z
  mul_comm := fun ⟨_, x⟩ ⟨_, y⟩ ↦ gradedMonoid_mk_cupUniv_comm x y
  natCast m := m • oneEven R Y
  natCast_zero := zero_smul _ _
  natCast_succ m := succ_nsmul _ m
  intCast m := m • oneEven R Y
  intCast_ofNat m := natCast_zsmul _ m
  intCast_negSucc_ofNat m := negSucc_zsmul _ m

-- `H^{ev} Y` is a commutative ring under the cup product.
example : CommRing (EvenCohomologyRing R Y) := inferInstance

variable {R Y}

/-- The unit of `H^{ev} Y` is `1 ∈ H^0 Y`. -/
theorem one_def : (1 : EvenCohomologyRing R Y) = DirectSum.of _ 0 (oneEven R Y) :=
  rfl

/-- The product of homogeneous classes in `H^{ev} Y` is their cup product. -/
theorem of_mul_of {p q : ℕ} (c : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ))
    (d : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * q : ℕ)) :
    (DirectSum.of _ p c * DirectSum.of _ q d : EvenCohomologyRing R Y) =
      DirectSum.of _ (p + q) (cupUniv R Y p q c d) :=
  DirectSum.of_mul_of (A := fun p : ℕ ↦
    cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ (2 * p : ℕ)) c d

end EvenCohomologyRing

end MMP
