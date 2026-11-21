import Atoms.Molecule.Construction.GrayProductMap
import Atoms.Molecule.Construction.Join
import Atoms.Molecule.Construction.SuspensionMap

universe u

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

section WithBot

variable {P P' : OGP.{u}}

theorem botSusp_withBotMap (f : P → P') (a : WithBot P) :
    botSusp P' (WithBot.map f a) = suspMap f (botSusp P a) := by
  induction a using WithBot.recBotCoe <;> rfl

end WithBot

section JoinMap

variable {P P' Q Q' : OGP.{u}}

def joinMap (f : P → P') (g : Q → Q') (p : join P Q) : join P' Q' :=
  ⟨(WithBot.map f p.1.1, WithBot.map g p.1.2), fun h => p.2 (Prod.ext
    (WithBot.map_eq_bot_iff.1 (congrArg Prod.fst h))
    (WithBot.map_eq_bot_iff.1 (congrArg Prod.snd h)))⟩

@[simp] theorem joinMap_val (f : P → P') (g : Q → Q') (p : join P Q) :
    (joinMap f g p).1 = (WithBot.map f p.1.1, WithBot.map g p.1.2) := rfl

theorem joinMap_id : joinMap (fun x : P => x) (fun y : Q => y) = fun p => p :=
  funext fun p => Subtype.ext (Prod.ext (congrFun WithBot.map_id p.1.1)
    (congrFun WithBot.map_id p.1.2))

theorem joinMap_comp {P'' Q'' : OGP.{u}} (f : P → P') (f' : P' → P'') (g : Q → Q')
    (g' : Q' → Q'') :
    joinMap (fun x => f' (f x)) (fun y => g' (g y)) = fun p => joinMap f' g' (joinMap f g p) :=
  funext fun p => Subtype.ext (Prod.ext (WithBot.map_map f' f p.1.1).symm
    (WithBot.map_map g' g p.1.2).symm)

theorem exists_joinMap_eq {f : P → P'} {g : Q → Q'} {a : WithBot P} {b : WithBot Q}
    {z : join P' Q'} (h₁ : WithBot.map f a = z.1.1) (h₂ : WithBot.map g b = z.1.2) :
    ∃ y : join P Q, y.1 = (a, b) ∧ joinMap f g y = z := by
  have hne : (a, b) ≠ ((⊥, ⊥) : WithBot P × WithBot Q) := by
    rintro ⟨⟩
    exact z.2 (Prod.ext h₁.symm h₂.symm)
  exact ⟨⟨(a, b), hne⟩, rfl, Subtype.ext (Prod.ext h₁ h₂)⟩

theorem monotone_joinMap {f : P → P'} {g : Q → Q'} (hf : Monotone f) (hg : Monotone g) :
    Monotone (joinMap f g) :=
  fun _ _ h => ⟨WithBot.monotone_map_iff.2 hf h.1, WithBot.monotone_map_iff.2 hg h.2⟩

theorem injective_joinMap {f : P → P'} {g : Q → Q'} (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (joinMap f g) :=
  fun _ _ h => Subtype.ext (Prod.ext (WithBot.map_injective hf (congrArg (·.1.1) h))
    (WithBot.map_injective hg (congrArg (·.1.2) h)))

theorem surjective_joinMap {f : P → P'} {g : Q → Q'} (hf : Function.Surjective f)
    (hg : Function.Surjective g) : Function.Surjective (joinMap f g) := by
  refine fun z => ⟨joinMap (Function.surjInv hf) (Function.surjInv hg) z, ?_⟩
  rw [← congrFun (joinMap_comp _ f _ g) z]
  simp only [Function.surjInv_eq, joinMap_id]

def suspProdMap (f : P → P') (g : Q → Q') :
    grayProduct (suspension P) (suspension Q) →
      grayProduct (suspension P') (suspension Q') :=
  fun w => (suspMap f w.1, suspMap g w.2)

theorem joinToGray_joinMap (f : P → P') (g : Q → Q') (p : join P Q) :
    joinToGray P' Q' (joinMap f g p) = suspProdMap f g (joinToGray P Q p) :=
  Prod.ext (botSusp_withBotMap f p.1.1) (botSusp_withBotMap g p.1.2)

theorem exists_joinToGray_eq_of_suspProdMap_eq {f : P → P'} {g : Q → Q'}
    {w : grayProduct (suspension P) (suspension Q)} {z' : join P' Q'}
    (h : suspProdMap f g w = joinToGray P' Q' z') :
    ∃ z, joinToGray P Q z = w ∧ joinMap f g z = z' := by
  obtain ⟨w₁, w₂⟩ := w
  have h₁ : suspMap f w₁ = botSusp P' z'.1.1 := congrArg Prod.fst h
  have h₂ : suspMap g w₂ = botSusp Q' z'.1.2 := congrArg Prod.snd h
  have hn₁ : w₁ ≠ .pole false := by
    rintro rfl
    exact ne_pole_false_of_botSusp_le h₁.symm.le rfl
  have hn₂ : w₂ ≠ .pole false := by
    rintro rfl
    exact ne_pole_false_of_botSusp_le h₂.symm.le rfl
  obtain ⟨a, rfl⟩ := exists_botSusp_eq hn₁
  obtain ⟨b, rfl⟩ := exists_botSusp_eq hn₂
  rw [← botSusp_withBotMap, botSusp_injective.eq_iff] at h₁ h₂
  obtain ⟨y, hy, hyz⟩ := exists_joinMap_eq h₁ h₂
  exact ⟨y, by rw [joinToGray, hy], hyz⟩

local instance (R S : OGP.{u}) : TopologicalSpace (SuspCarrier R × SuspCarrier S) :=
  (grayProduct (suspension R) (suspension S)).topologicalSpace

local instance (R S : OGP.{u}) : Topology.IsUpperSet (SuspCarrier R × SuspCarrier S) :=
  (grayProduct (suspension R) (suspension S)).isUpperSet

theorem isClosedMap_joinMap {f : P → P'} {g : Q → Q'} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (joinMap f g) := by
  have hΦ := IsUpperSet.isClosedMap_iff_fibration.1
    (isClosedMap_prodMap (P := suspension P) (P' := suspension P')
      (Q := suspension Q) (Q' := suspension Q') (isClosedMap_suspMap hf) (isClosedMap_suspMap hg))
  refine IsUpperSet.isClosedMap_iff_fibration.2 fun p z' h => ?_
  have hle : joinToGray P' Q' z' ≤ suspProdMap f g (joinToGray P Q p) := by
    rw [← joinToGray_joinMap]
    exact joinToGray_le_joinToGray_iff.2 h
  obtain ⟨w, hw, hwz⟩ := hΦ hle
  obtain ⟨z, rfl, rfl⟩ := exists_joinToGray_eq_of_suspProdMap_eq hwz
  exact ⟨z, joinToGray_le_joinToGray_iff.1 hw, rfl⟩

theorem finalOn_joinPre {f : P → P'} {g : Q → Q'}
    {W : LowerSet (grayProduct (suspension P) (suspension Q))}
    {W' : LowerSet (grayProduct (suspension P') (suspension Q'))}
    (h : FinalOn (suspProdMap f g) W W') :
    FinalOn (joinMap f g) (joinPre P Q W) (joinPre P' Q' W') := by
  have hs := joinToGray_joinMap f g
  have hmem (q : join P Q) (z' : join P' Q') :
      q ∈ (joinPre P Q W : Set (join P Q)) ∩ joinMap f g ⁻¹' Ici z' ↔
        joinToGray P Q q ∈ (W : Set _) ∩ suspProdMap f g ⁻¹' Ici (joinToGray P' Q' z') := by
    simp only [mem_inter_iff, SetLike.mem_coe, mem_joinPre, mem_preimage, mem_Ici]
    rw [← hs, joinToGray_le_joinToGray_iff]
  have hlift (z' : join P' Q') (w : grayProduct (suspension P) (suspension Q))
      (hw : w ∈ (W : Set _) ∩ suspProdMap f g ⁻¹' Ici (joinToGray P' Q' z')) :
      ∃ q ∈ (joinPre P Q W : Set (join P Q)) ∩ joinMap f g ⁻¹' Ici z',
        joinToGray P Q q = w := by
    obtain ⟨q', hq'⟩ := exists_joinToGray_eq_of_le hw.2
    obtain ⟨q, rfl, -⟩ := exists_joinToGray_eq_of_suspProdMap_eq hq'.symm
    exact ⟨q, (hmem q z').2 hw, rfl⟩
  refine ⟨fun z hz => by rw [SetLike.mem_coe, mem_joinPre, hs]; exact h.1 hz, fun z' hz' => ?_⟩
  obtain ⟨⟨w₀, hw₀⟩, hconn⟩ := h.2 (joinToGray P' Q' z') hz'
  obtain ⟨q₀, hq₀, -⟩ := hlift z' w₀ hw₀
  refine ⟨⟨q₀, hq₀⟩, IsUpperSet.isPreconnected_iff_reflTransGen.2 fun a ha b hb => ?_⟩
  have hzz := IsUpperSet.isPreconnected_iff_reflTransGen.1 hconn
    (joinToGray P Q a) ((hmem a z').1 ha) (joinToGray P Q b) ((hmem b z').1 hb)
  have key : ∀ v, Relation.ReflTransGen
      (fun x y => x ∈ (W : Set _) ∩ suspProdMap f g ⁻¹' Ici (joinToGray P' Q' z') ∧
        y ∈ (W : Set _) ∩ suspProdMap f g ⁻¹' Ici (joinToGray P' Q' z') ∧ (x ≤ y ∨ y ≤ x))
      (joinToGray P Q a) v →
      ∃ q, joinToGray P Q q = v ∧ Relation.ReflTransGen
        (fun x y => x ∈ (joinPre P Q W : Set (join P Q)) ∩ joinMap f g ⁻¹' Ici z' ∧
          y ∈ (joinPre P Q W : Set (join P Q)) ∩ joinMap f g ⁻¹' Ici z' ∧ (x ≤ y ∨ y ≤ x))
        a q := by
    intro v hv
    induction hv with
    | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
    | tail _ hstep ih =>
      obtain ⟨q, rfl, hq⟩ := ih
      obtain ⟨q', hq', rfl⟩ := hlift z' _ hstep.2.1
      exact ⟨q', rfl, hq.tail ⟨(hmem q z').2 hstep.1, hq',
        hstep.2.2.imp joinToGray_le_joinToGray_iff.1 joinToGray_le_joinToGray_iff.1⟩⟩
  obtain ⟨q, hq, hr⟩ := key _ hzz
  rwa [joinToGray_injective hq] at hr

theorem isMap_joinMap (hP : IsRDC P) (hP' : IsRDC P') (hQ : IsRDC Q) (hQ' : IsRDC Q')
    {f : P → P'} {g : Q → Q'} (hf : IsMap f) (hg : IsMap g) : IsMap (joinMap f g) := by
  have hΦ : IsMap (suspProdMap f g) :=
    isMap_prodMap (isRDC_suspension hP) (isRDC_suspension hP') (isRDC_suspension hQ)
      (isRDC_suspension hQ') (isMap_suspMap hP hf) (isMap_suspMap hQ hg)
  refine ⟨isClosedMap_joinMap hf.isClosedMap hg.isClosedMap, fun z n α => ?_⟩
  rw [← joinPre_Iic z, ← joinPre_boundary_succ, ← joinPre_Iic (joinMap f g z),
    ← joinPre_boundary_succ, joinToGray_joinMap]
  exact finalOn_joinPre (hΦ.finalOn (joinToGray P Q z) (n + 1) α)

theorem functor_isFibered_joinMap {f : P → P'} {g : Q → Q'} (hf : Monotone f) (hg : Monotone g)
    [hf.functor.IsFibered] [hg.functor.IsFibered] :
    (monotone_joinMap hf hg).functor.IsFibered := by
  have := hf.withBotMap_functor_isFibered
  have := hg.withBotMap_functor_isFibered
  refine (Monotone.functor_isFibered_iff _).2 fun x w hw => ?_
  obtain ⟨a', ha', ha'w, ha'max⟩ :=
    Monotone.exists_lift (WithBot.monotone_map_iff.2 hf) (join_le_iff.1 hw).1
  obtain ⟨b', hb', hb'w, hb'max⟩ :=
    Monotone.exists_lift (WithBot.monotone_map_iff.2 hg) (join_le_iff.1 hw).2
  obtain ⟨y, hy, hyw⟩ := exists_joinMap_eq ha'w hb'w
  exact ⟨y, join_le_iff.2 ⟨hy ▸ ha', hy ▸ hb'⟩, hyw, fun z hz hzw => join_le_iff.2
    ⟨hy ▸ ha'max _ (join_le_iff.1 hz).1 (join_le_iff.1 hzw).1,
      hy ▸ hb'max _ (join_le_iff.1 hz).2 (join_le_iff.1 hzw).2⟩⟩

theorem isMorphism_joinMap {f : P → P'} {g : Q → Q'} (hf : IsMorphism f) (hg : IsMorphism g) :
    IsMorphism (joinMap f g) := by
  refine ⟨fun p α => ?_⟩
  have hΦ := (isMorphism_prodMap hf.withBotMap hg.withBotMap).bijOn_faces p.1 α
  refine ⟨fun q hq => mem_faces_join.2 (hΦ.mapsTo (mem_faces_join.1 hq)),
    fun q₁ hq₁ q₂ hq₂ h => Subtype.ext
      (hΦ.injOn (mem_faces_join.1 hq₁) (mem_faces_join.1 hq₂) (congrArg Subtype.val h)),
    fun z' hz' => ?_⟩
  obtain ⟨⟨a, b⟩, hab, he⟩ := hΦ.surjOn (mem_faces_join.1 hz')
  obtain ⟨q, hq, hqz⟩ := exists_joinMap_eq (congrArg Prod.fst he) (congrArg Prod.snd he)
  exact ⟨q, mem_faces_join.2 (hq ▸ hab), hqz⟩

def join.map (f : P ⟶ P') (g : Q ⟶ Q') : join P Q ⟶ join P' Q' :=
  ConcreteCategory.ofHom ⟨joinMap f g, isMorphism_joinMap (isMorphism f) (isMorphism g)⟩

@[simp] theorem join.map_apply (f : P ⟶ P') (g : Q ⟶ Q') (p : join P Q) :
    join.map f g p = joinMap f g p :=
  rfl

def join.mapIso (e : P ≅ P') (e' : Q ≅ Q') : join P Q ≅ join P' Q' where
  hom := join.map e.hom e'.hom
  inv := join.map e.inv e'.inv
  hom_inv_id := by
    ext p
    refine (congrFun (joinMap_comp e.hom e.inv e'.hom e'.inv) p).symm.trans ?_
    simp only [Iso.hom_inv_id_apply]
    exact congrFun joinMap_id p
  inv_hom_id := by
    ext p
    refine (congrFun (joinMap_comp e.inv e.hom e'.inv e'.hom) p).symm.trans ?_
    simp only [Iso.inv_hom_id_apply]
    exact congrFun joinMap_id p

@[simp] theorem join.mapIso_hom_apply (e : P ≅ P') (e' : Q ≅ Q') (p : join P Q) :
    (join.mapIso e e').hom p = joinMap e.hom e'.hom p :=
  rfl

instance (f : P ⟶ P') (g : Q ⟶ Q') [IsInclusion f] [IsInclusion g] :
    IsInclusion (join.map f g) :=
  ⟨injective_joinMap (IsInclusion.injective (f := f)) (IsInclusion.injective (f := g))⟩

end JoinMap

end Atoms.Molecule.OGP
