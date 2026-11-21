import Atoms.Molecule.RegularComplex.Comap
import Atoms.Molecule.RegularComplex.Morphism

universe u v w

open Order Set Topology

namespace Atoms.Molecule.OGP

section LocalEmbedding

variable {P : OGP.{u}} {Q : OGP.{v}}

theorem IsLocalEmbedding.isRDC {f : P → Q} (hf : IsMorphism f) (hle : IsLocalEmbedding f)
    (hQ : IsRDC Q) : IsRDC P := fun x =>
  hf.isMoleculeIn_of_injOn (fun _ hy _ hz h => hle.injOn hy hz h) (hf.image_Iic x).symm (hQ (f x))

end LocalEmbedding

section Pullback

variable {P : OGP.{u}} {Q : OGP.{v}} {V : OGP.{w}} {c : P → Q} {f : V → Q}

private abbrev PullbackCarrier (c : P → Q) (f : V → Q) : Type (max u w) :=
  {p : P × V // c p.1 = f p.2}

private theorem pb_le_iff {p q : PullbackCarrier c f} : p ≤ q ↔ p.1.1 ≤ q.1.1 ∧ p.1.2 ≤ q.1.2 :=
  Iff.rfl

private theorem pb_exists_le (hc : Monotone c) (hf : IsLocalEmbedding f) {p : PullbackCarrier c f}
    {x : P} (hx : x ≤ p.1.1) : ∃ q ≤ p, q.1.1 = x := by
  obtain ⟨y, hy, he⟩ :=
    IsUpperSet.isClosedMap_iff_fibration.1 hf.isClosedMap ((hc hx).trans p.2.le)
  exact ⟨⟨(x, y), he.symm⟩, pb_le_iff.2 ⟨hx, hy⟩, rfl⟩

private theorem pb_eq_of_fst_eq (hf : IsLocalEmbedding f) {p q r : PullbackCarrier c f}
    (hp : p ≤ r) (hq : q ≤ r) (h : p.1.1 = q.1.1) : p = q :=
  Subtype.ext (Prod.ext h (hf.injOn (pb_le_iff.1 hp).2 (pb_le_iff.1 hq).2
    (p.2.symm.trans ((congrArg c h).trans q.2))))

private theorem pb_le_of_fst_le (hc : Monotone c) (hf : IsLocalEmbedding f)
    {p q r : PullbackCarrier c f} (hp : p ≤ r) (hq : q ≤ r) (h : p.1.1 ≤ q.1.1) : p ≤ q := by
  obtain ⟨p', hp'q, hp'⟩ := pb_exists_le hc hf h
  exact pb_eq_of_fst_eq hf (hp'q.trans hq) hp hp' ▸ hp'q

private theorem pb_fst_lt (hf : IsLocalEmbedding f) {p q : PullbackCarrier c f} (h : p < q) :
    p.1.1 < q.1.1 :=
  (pb_le_iff.1 h.le).1.lt_of_ne fun he => h.ne (pb_eq_of_fst_eq hf h.le le_rfl he)

private theorem pb_lt_of_fst_lt (hc : Monotone c) (hf : IsLocalEmbedding f)
    {p q r : PullbackCarrier c f} (hp : p ≤ r) (hq : q ≤ r) (h : p.1.1 < q.1.1) : p < q :=
  (pb_le_of_fst_le hc hf hp hq h.le).lt_of_ne fun he => h.ne (congrArg (fun s => s.1.1) he)

private theorem pb_fst_covBy (hc : Monotone c) (hf : IsLocalEmbedding f)
    {p q : PullbackCarrier c f} (h : p ⋖ q) : p.1.1 ⋖ q.1.1 := by
  refine ⟨pb_fst_lt hf h.lt, fun x hpx hxq => ?_⟩
  obtain ⟨r, hrq, rfl⟩ := pb_exists_le hc hf hxq.le
  exact h.2 (pb_lt_of_fst_lt hc hf h.le hrq hpx) (pb_lt_of_fst_lt hc hf hrq le_rfl hxq)

private theorem pb_covBy_of_fst_covBy (hf : IsLocalEmbedding f) {p q : PullbackCarrier c f}
    (hp : p ≤ q) (h : p.1.1 ⋖ q.1.1) : p ⋖ q :=
  ⟨hp.lt_of_ne fun he => h.ne (congrArg (fun s => s.1.1) he),
    fun _ hpr hrq => h.2 (pb_fst_lt hf hpr) (pb_fst_lt hf hrq)⟩

private abbrev pullbackGradeMinOrder (hc : Monotone c) (hf : IsLocalEmbedding f) :
    GradeMinOrder ℕ (PullbackCarrier c f) where
  grade p := grade ℕ p.1.1
  grade_strictMono _ _ h := grade_strictMono (pb_fst_lt hf h)
  covBy_grade _ _ h := (pb_fst_covBy hc hf h).grade ℕ
  isMin_grade p h := IsMin.grade ℕ fun x hx => by
    obtain ⟨q, hqp, rfl⟩ := pb_exists_le hc hf hx
    exact (pb_le_iff.1 (h hqp)).1

@[implicit_reducible] def pullback (hc : Monotone c) (hf : IsLocalEmbedding f) : OGP.{max u w} where
  carrier := PullbackCarrier c f
  gradeMinOrderCarrier := pullbackGradeMinOrder hc hf
  orient h := P.orient (pb_fst_covBy hc hf h)

variable (hc : Monotone c) (hf : IsLocalEmbedding f)

transfer_instances pullback hc hf with DecidableEq DecidableLE Fintype

def pullbackMk (x : P) (y : V) (h : c x = f y) : pullback hc hf := ⟨(x, y), h⟩

def pullbackFst : pullback hc hf → P := fun p : PullbackCarrier c f => p.1.1

def pullbackSnd : pullback hc hf → V := fun p : PullbackCarrier c f => p.1.2

@[simp] theorem pullbackFst_pullbackMk (x : P) (y : V) (h : c x = f y) :
    pullbackFst hc hf (pullbackMk hc hf x y h) = x :=
  rfl

@[simp] theorem pullbackSnd_pullbackMk (x : P) (y : V) (h : c x = f y) :
    pullbackSnd hc hf (pullbackMk hc hf x y h) = y :=
  rfl

theorem pullback_condition : c ∘ pullbackFst hc hf = f ∘ pullbackSnd hc hf :=
  funext fun p : PullbackCarrier c f => p.2

theorem pullback_condition_apply (p : pullback hc hf) :
    c (pullbackFst hc hf p) = f (pullbackSnd hc hf p) :=
  congrFun (pullback_condition hc hf) p

@[ext] theorem pullback_ext {p q : pullback hc hf} (h₁ : pullbackFst hc hf p = pullbackFst hc hf q)
    (h₂ : pullbackSnd hc hf p = pullbackSnd hc hf q) : p = q :=
  Subtype.ext (Prod.ext h₁ h₂)

theorem pullback_le_iff {p q : pullback hc hf} :
    p ≤ q ↔ pullbackFst hc hf p ≤ pullbackFst hc hf q ∧ pullbackSnd hc hf p ≤ pullbackSnd hc hf q :=
  Iff.rfl

@[simp] theorem grade_pullback (p : pullback hc hf) : grade ℕ p = grade ℕ (pullbackFst hc hf p) :=
  rfl

theorem monotone_pullbackSnd : Monotone (pullbackSnd hc hf) := fun _ _ h =>
  ((pullback_le_iff hc hf).1 h).2

theorem isLocalEmbedding_pullbackFst : IsLocalEmbedding (pullbackFst hc hf) := fun p => by
  have hcl : closure ({p} : Set (pullback hc hf)) = Iic p := IsUpperSet.closure_singleton
  have hmem (q : closure ({p} : Set (pullback hc hf))) : (q : pullback hc hf) ≤ p :=
    (Set.ext_iff.1 hcl q.1).1 q.2
  have hmono : Monotone ((closure ({p} : Set (pullback hc hf))).domRestrict
      (pullbackFst hc hf)) := fun _ _ hab => ((pullback_le_iff hc hf).1 hab).1
  refine .of_continuous_injective_isClosedMap (IsUpperSet.monotone_iff_continuous.1 hmono)
    (fun a b h => Subtype.ext (pb_eq_of_fst_eq hf (hmem a) (hmem b) h))
    (IsUpperSet.isClosedMap_iff_fibration.2 fun a x hx => ?_)
  obtain ⟨q, hqa, rfl⟩ := pb_exists_le hc hf hx
  exact ⟨⟨q, (Set.ext_iff.1 hcl q).2 (le_trans hqa (hmem a))⟩, hqa, rfl⟩

theorem isMorphism_pullbackFst : IsMorphism (pullbackFst hc hf) where
  bijOn_faces p α := by
    refine ⟨fun q ⟨h, hα⟩ => ⟨pb_fst_covBy hc hf h, hα⟩,
      fun q hq r hr he => pb_eq_of_fst_eq hf hq.1.le hr.1.le he, fun x ⟨hx, hα⟩ => ?_⟩
    obtain ⟨q, hqp, rfl⟩ := pb_exists_le hc hf hx.le
    exact ⟨q, ⟨pb_covBy_of_fst_covBy hf hqp hx, hα⟩, rfl⟩

theorem image_pullbackFst_preimage_pullbackSnd (S : Set V) :
    pullbackFst hc hf '' (pullbackSnd hc hf ⁻¹' S) = c ⁻¹' (f '' S) := by
  ext x
  refine ⟨?_, fun ⟨y, hy, he⟩ => ⟨pullbackMk hc hf x y he.symm, hy, rfl⟩⟩
  rintro ⟨p, hp, rfl⟩
  exact ⟨pullbackSnd hc hf p, hp, (pullback_condition_apply hc hf p).symm⟩

private theorem injOn_pullbackFst (y : V) :
    InjOn (pullbackFst hc hf) (pullbackSnd hc hf ⁻¹' (LowerSet.Iic y : Set V)) :=
  fun p hp q hq h => pullback_ext hc hf h (hf.injOn hp hq
    ((pullback_condition_apply hc hf p).symm.trans ((congrArg c h).trans
      (pullback_condition_apply hc hf q))))

end Pullback

variable {P : OGP.{u}} {Q : OGP.{v}} {V : OGP.{w}}

theorem IsComap.isComap_pullbackSnd {c : P → Q} (hc : IsComap c) {f : V → Q} (hf : IsMorphism f)
    (hle : IsLocalEmbedding f) : IsComap (pullbackSnd hc.monotone hle) where
  monotone := monotone_pullbackSnd hc.monotone hle
  isMoleculeIn_Iic y := by
    refine (isMorphism_pullbackFst hc.monotone hle).isMoleculeIn_of_injOn
      (injOn_pullbackFst hc.monotone hle y) ?_ (hc.isMoleculeIn_Iic (f y))
    rw [coe_lowerPreimage, coe_lowerPreimage, image_pullbackFst_preimage_pullbackSnd,
      hf.image_Iic]
  boundary_Iic y n α := by
    have hi := injOn_pullbackFst hc.monotone hle y
    have hW : (lowerPreimage hc.monotone (.Iic (f y)) : Set P) = pullbackFst hc.monotone hle ''
        (lowerPreimage (monotone_pullbackSnd hc.monotone hle) (.Iic y) : Set _) := by
      rw [coe_lowerPreimage, coe_lowerPreimage, image_pullbackFst_preimage_pullbackSnd,
        hf.image_Iic]
    refine eq_of_image_eq_of_injOn hi (fun _ hp => boundary_le (.Iic y) n α hp)
      (boundary_le _ n α) ?_
    rw [(isMorphism_pullbackFst hc.monotone hle).image_boundary_of_injOn hi hW,
      ← hc.boundary_Iic, coe_lowerPreimage, coe_lowerPreimage,
      image_pullbackFst_preimage_pullbackSnd,
      hf.image_boundary_of_injOn (fun _ ha _ hb h => hle.injOn ha hb h) (hf.image_Iic y).symm]

section Lift

variable {c : P → Q} {f : V → Q} (hc : Monotone c) (hf : IsLocalEmbedding f) {S : Type*}

def pullbackLift (g : S → P) (k : S → V) (e : c ∘ g = f ∘ k) : S → pullback hc hf :=
  fun s => pullbackMk hc hf (g s) (k s) (congrFun e s)

variable {g : S → P} {k : S → V} (e : c ∘ g = f ∘ k)

@[simp] theorem pullbackFst_comp_pullbackLift :
    pullbackFst hc hf ∘ pullbackLift hc hf g k e = g :=
  rfl

@[simp] theorem pullbackSnd_comp_pullbackLift :
    pullbackSnd hc hf ∘ pullbackLift hc hf g k e = k :=
  rfl

theorem pullbackLift_unique (l : S → pullback hc hf) (h₁ : pullbackFst hc hf ∘ l = g)
    (h₂ : pullbackSnd hc hf ∘ l = k) : l = pullbackLift hc hf g k e :=
  funext fun s => pullback_ext hc hf (congrFun h₁ s) (congrFun h₂ s)

theorem monotone_pullbackLift [Preorder S] (hg : Monotone g) (hk : Monotone k) :
    Monotone (pullbackLift hc hf g k e) := fun _ _ h =>
  (pullback_le_iff hc hf).2 ⟨hg h, hk h⟩

end Lift

end Atoms.Molecule.OGP
