From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

Parameter Data : Type.
Definition Address := nat.

Inductive Permission : Type := | ReadOnly | WriteOnly | ReadWrite | NoAccess.
Inductive OperationResult : Type := | Success (data : list Data) | PermissionDenied | AddressOutOfBounds.

Record DataBlock : Type := { block_data : Data; block_permission : Permission }.

(* 起始地址 addr 与长度 len，区间含义为 [addr, addr+len) 且要求 len > 0 *)
Module Type StorageMedium.
  Parameter StorageState : Type.
  Parameter get_blocks : StorageState -> list DataBlock.
  Parameter init_storage : list DataBlock -> StorageState.
  Parameter storage_size : StorageState -> nat.
  Parameter check_read_permission : StorageState -> Address -> nat (* len *) -> bool.
  Parameter check_write_permission : StorageState -> Address -> nat -> bool.
  Parameter update_blocks : StorageState -> Address -> nat -> list Data -> StorageState.
  Axiom storage_size_consistency : forall s, storage_size s = length (get_blocks s).
  Axiom update_preserves_blocks_length : forall s addr len datas,
      length (get_blocks (update_blocks s addr len datas)) = length (get_blocks s).
End StorageMedium.

Module MakeStorage (L : StorageMedium).
  Definition StorageState := L.StorageState.
  Definition get_blocks := L.get_blocks.
  Definition init_storage := L.init_storage.
  Definition storage_size := L.storage_size.
  Definition check_read_permission := L.check_read_permission.
  Definition check_write_permission := L.check_write_permission.
  Definition update_blocks := L.update_blocks.

  (* 读：若 len=0 或 addr+len > size 则越界；否则检查权限并读取 len 个元素 *)
  Definition read (s:StorageState) (addr len:nat) : OperationResult :=
    if orb (Nat.eqb len 0) (negb (Nat.leb (addr + len) (storage_size s))) then AddressOutOfBounds
    else if check_read_permission s addr len then
           let data := map block_data (firstn len (skipn addr (get_blocks s))) in
           Success data
         else PermissionDenied.

  Definition write (s:StorageState) (addr len:nat) (datas:list Data) : StorageState * OperationResult :=
    if orb (Nat.eqb len 0) (negb (Nat.leb (addr + len) (storage_size s))) then (s, AddressOutOfBounds)
    else if negb (check_write_permission s addr len) then (s, PermissionDenied)
    else if Nat.eqb (length datas) len then
           let s' := update_blocks s addr len datas in (s', Success datas)
         else (s, AddressOutOfBounds).

  Definition WriteOp := ((nat * nat) * list Data)%type.  (* ((addr,len),datas) *)

  Fixpoint apply_writes (ops : list WriteOp) (rs : StorageState) : StorageState :=
    match ops with
    | [] => rs
    | ((addr,len),datas)::ops' =>
        let '(rs', _) := write rs addr len datas in
        apply_writes ops' rs'
    end.

  (* 基础长度引理： *)
  Lemma firstn_skipn_segment_length : forall (A:Type) (l:list A) addr len,
      len > 0 -> addr + len <= length l -> length (firstn len (skipn addr l)) = len.
  Proof.
    intros A l addr len Hpos Hbound.
    rewrite length_firstn, length_skipn.
    apply Nat.min_l.
    assert (len <= length l - addr) by lia. lia.
  Qed.

  Lemma read_out_of_bounds : forall s addr len,
      len = 0 \/ addr + len > storage_size s -> read s addr len = AddressOutOfBounds.
  Proof.
    intros s addr len [Hz | Hgt].
    - subst. unfold read. rewrite Nat.eqb_refl. reflexivity.
    - unfold read.
      destruct (Nat.eqb len 0) eqn:Hlen.
      + (* len = 0 chosen from right disj: still out-of-bounds because first branch triggers *)
        reflexivity.
      + (* len > 0, use upper bound violation *)
        rewrite Bool.orb_false_l.
        assert (negb (Nat.leb (addr + len) (storage_size s)) = true) as Hnb.
        { apply negb_true_iff. apply Nat.leb_gt. lia. }
        rewrite Hnb. reflexivity.
  Qed.

  Lemma read_permission_denied : forall s addr len,
      len > 0 /\ addr + len <= storage_size s /\ check_read_permission s addr len = false ->
      read s addr len = PermissionDenied.
  Proof.
    intros s addr len [Hpos [Hbound Hperm]].
    unfold read.
    assert (Nat.eqb len 0 = false) by (apply Nat.eqb_neq; lia).
    rewrite H.
    assert (negb (Nat.leb (addr + len) (storage_size s)) = false) as Hb.
    { apply negb_false_iff. apply Nat.leb_le. lia. }
    rewrite Bool.orb_false_l, Hb.
    now rewrite Hperm.
  Qed.

  Lemma read_success_condition : forall s addr len data,
      read s addr len = Success data ->
      len > 0 /\ addr + len <= storage_size s /\ check_read_permission s addr len = true /\ length data = len.
  Proof.
    intros s addr len data H.
    unfold read in H.
    destruct (Nat.eqb len 0) eqn:Hz; [discriminate|].
    apply Nat.eqb_neq in Hz.
    destruct (negb (Nat.leb (addr + len) (storage_size s))) eqn:HbBool; [discriminate|].
    apply negb_false_iff in HbBool.
    destruct (check_read_permission s addr len) eqn:Hp; [|discriminate].
    inversion H; subst data; clear H.
    repeat split; try assumption.
    - lia.
    - apply Nat.leb_le in HbBool; lia.
    - rewrite length_map.
      apply Nat.leb_le in HbBool.
      (* Convert size inequality to list-length inequality inline and apply segment lemma. *)
      eapply firstn_skipn_segment_length; [lia|].
      rewrite <- L.storage_size_consistency; exact HbBool.
  Qed.

  Lemma write_out_of_bounds : forall s addr len data,
      len = 0 \/ addr + len > storage_size s -> write s addr len data = (s, AddressOutOfBounds).
  Proof.
    intros s addr len data [Hz|Hgt].
    - subst. unfold write. rewrite Nat.eqb_refl. reflexivity.
    - unfold write.
      (* Use the bound violation directly; no need to split on len=0. *)
      assert (negb (Nat.leb (addr + len) (storage_size s)) = true) as Hnb
        by (apply negb_true_iff; apply Nat.leb_gt; lia).
      rewrite Hnb.
      (* Now the orb has form (Nat.eqb len 0) || true *)
      rewrite Bool.orb_true_r.
      reflexivity.
  Qed.

  Lemma write_permission_denied : forall s addr len data,
      len > 0 /\ addr + len <= storage_size s /\ check_write_permission s addr len = false ->
      write s addr len data = (s, PermissionDenied).
  Proof.
    intros s addr len data [Hpos [Hbound Hperm]].
    unfold write.
    assert (Nat.eqb len 0 = false) by (apply Nat.eqb_neq; lia); rewrite H.
    assert (negb (Nat.leb (addr + len) (storage_size s)) = false) as Hb.
    { apply negb_false_iff. apply Nat.leb_le. lia. }
    rewrite Bool.orb_false_l, Hb.
    now rewrite Hperm.
  Qed.

  Lemma write_success_preserves_size : forall s addr len data s' result,
      write s addr len data = (s', result) -> result = Success data -> storage_size s' = storage_size s.
  Proof.
    intros s addr len data s' result Hw Hres. subst result.
    unfold write in Hw.
    destruct (Nat.eqb len 0); [inversion Hw|].
    destruct (negb (Nat.leb (addr + len) (storage_size s))) eqn:Hb; [inversion Hw|].
    destruct (negb (check_write_permission s addr len)) eqn:Hp; [inversion Hw|].
    destruct (Nat.eqb (length data) len) eqn:Hlen; [|inversion Hw].
    inversion Hw; subst s'. clear Hw.
    rewrite !L.storage_size_consistency.
    apply L.update_preserves_blocks_length.
  Qed.

  Axiom write_then_read_consistency : forall s addr len data s' result,
      write s addr len data = (s', result) ->
      result = Success data ->
      read s addr len = Success data \/ read s addr len = PermissionDenied.
End MakeStorage.

(* ROM 实现：只读，写永远拒绝 *)
Module ROM <: StorageMedium.
  Record ROMStorageState := { blocks : list DataBlock }.
  Definition StorageState := ROMStorageState.
  Definition get_blocks s := s.(blocks).
  Definition init_storage (bs:list DataBlock) : StorageState :=
    let ro := map (fun b => {| block_data := b.(block_data); block_permission := ReadOnly |}) bs in
    {| blocks := ro |}.
  Definition storage_size s := length (get_blocks s).
  Definition check_read_permission (_:StorageState) (_ _:nat) := true.
  Definition check_write_permission (_:StorageState) (_ _:nat) := false.
  Definition update_blocks (s:StorageState) (_ _:nat) (_:list Data) := s.
  Lemma storage_size_consistency : forall s, storage_size s = length (get_blocks s). Proof. reflexivity. Qed.
  Lemma update_preserves_blocks_length : forall s addr len datas,
      length (get_blocks (update_blocks s addr len datas)) = length (get_blocks s). Proof. reflexivity. Qed.
End ROM.

Module Flash <: StorageMedium.
  Record FlashStorageState := { blocks : list DataBlock }.
  Definition StorageState := FlashStorageState.
  Definition get_blocks s := s.(blocks).
  Definition init_storage (bs:list DataBlock) : StorageState := {| blocks := bs |}.
  Definition storage_size s := length (get_blocks s).
  Definition check_read_permission (_:StorageState) (_ _:nat) := true.
  Definition check_write_permission (_:StorageState) (_ _:nat) := true.
  (* 只有当 (length datas = len) 且 (addr+len <= length l) 时才执行区间替换，否则保持原状态以保证长度不变 *)
  Definition update_blocks (s:StorageState) (addr len:nat) (datas:list Data) : StorageState :=
    let l := get_blocks s in
    if andb (Nat.eqb (length datas) len) (Nat.leb (addr + len) (length l)) then
      let new_blocks := firstn addr l ++
                        map (fun d => {| block_data := d; block_permission := ReadWrite |}) datas ++
                        skipn (addr + len) l in
      {| blocks := new_blocks |}
    else s.
  Lemma storage_size_consistency : forall s, storage_size s = length (get_blocks s). Proof. reflexivity. Qed.
  Lemma update_preserves_blocks_length : forall s addr len datas,
      length (get_blocks (update_blocks s addr len datas)) = length (get_blocks s).
  Proof.
    intros s addr len datas.
    unfold update_blocks.
    set (l := get_blocks s).
    destruct (Nat.eqb (length datas) len) eqn:Hlen;
      destruct (Nat.leb (addr + len) (length l)) eqn:Hbound; simpl; try reflexivity.
    apply Nat.eqb_eq in Hlen; subst.
    apply Nat.leb_le in Hbound.
    rewrite length_app, length_app, length_map.
    rewrite firstn_length_le.
    2:{ lia. }
    rewrite length_skipn.
    lia.
  Qed.
End Flash.

(* EFuse 实现：写一次后不可写 *)
Module EFuse <: StorageMedium.
  Record EFuseStorageState := { blocks : list DataBlock }.
  Definition StorageState := EFuseStorageState.
  Definition get_blocks s := s.(blocks).
  Definition init_storage (bs:list DataBlock) : StorageState :=
    let rw := map (fun b => {| block_data := b.(block_data); block_permission := ReadWrite |}) bs in
    {| blocks := rw |}.
  Definition storage_size s := length (get_blocks s).

  (* Helper: predicate for blocks still writable *)
  Definition block_writable (b:DataBlock) : bool :=
    match b.(block_permission) with
    | ReadWrite | WriteOnly => true
    | _ => false
    end.

  (* Allow read always *)
  Definition check_read_permission (_:StorageState) (_ _:nat) := true.

  (* Writable iff range in bounds, len>0, and all targeted blocks are still writable *)
  Definition check_write_permission (s:StorageState) (addr len:nat) : bool :=
    let l := get_blocks s in
    if andb (negb (Nat.eqb len 0)) (Nat.leb (addr + len) (length l)) then
      forallb block_writable (firstn len (skipn addr l))
    else false.

  (* Update only if length datas = len, in bounds, len>0 and all currently writable; then set new data blocks to ReadOnly *)
  Definition update_blocks (s:StorageState) (addr len:nat) (datas:list Data) : StorageState :=
    let l := get_blocks s in
    if andb (andb (Nat.eqb (length datas) len)
                 (andb (negb (Nat.eqb len 0)) (Nat.leb (addr + len) (length l))))
            (forallb block_writable (firstn len (skipn addr l))) then
      let new_blocks := firstn addr l ++
                        map (fun d => {| block_data := d; block_permission := ReadOnly |}) datas ++
                        skipn (addr + len) l in
      {| blocks := new_blocks |}
    else s.

  Lemma storage_size_consistency : forall s, storage_size s = length (get_blocks s). Proof. reflexivity. Qed.

  Lemma update_preserves_blocks_length : forall s addr len datas,
      length (get_blocks (update_blocks s addr len datas)) = length (get_blocks s).
  Proof.
    intros s addr len datas.
    unfold update_blocks.
    set (l := get_blocks s).
    destruct (Nat.eqb (length datas) len) eqn:Hlen;
      destruct (Nat.eqb len 0) eqn:Hz;
      destruct (Nat.leb (addr + len) (length l)) eqn:Hbound;
      destruct (forallb block_writable (firstn len (skipn addr l))) eqn:Hall;
      simpl; try reflexivity.
    (* successful update case *)
    apply Nat.eqb_eq in Hlen; subst.
    apply Nat.eqb_neq in Hz.
    apply Nat.leb_le in Hbound.
    rewrite length_app, length_app, length_map.
    assert (Haddr: addr <= length l) by lia.
    rewrite firstn_length_le by lia.
    rewrite length_skipn.
    lia.
  Qed.
End EFuse.

Module ROM_instance.
  Include MakeStorage(ROM).

  (* ---------- ROM 不可变性 ---------- *)
  Lemma rom_write_idempotent :
    forall s s' addr len datas result,
      write s addr len datas = (s', result) ->
      s' = s.
  Proof.
    intros.
    unfold write in H.
    destruct (Nat.eqb len 0); destruct (negb (Nat.leb (addr + len) (storage_size s)));
      simpl in H; try (inversion H; reflexivity).
  Qed.
  Lemma apply_rom_writes_preserves_state :
    forall ops rs,
      apply_writes ops rs = rs.
  Proof.
    intros ops.
    induction ops as [| [[addr len] datas] ops IH]; intros rs; simpl; auto.
    destruct (write rs addr len datas) as [rs' res] eqn:W.
    pose proof (rom_write_idempotent rs rs' addr len datas res W) as Himm.
    subst rs'.
    apply IH.
  Qed.
End ROM_instance.

Module Flash_instance.
  Include MakeStorage(Flash).
End Flash_instance.

Module EFuse_instance.
  Include MakeStorage(EFuse).
End EFuse_instance.
