From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
Require Import StorageMedium AlgorithmKit.

Module MakeSecureBoot (Sig : DigitalSignature).

  (* ========== 存储映射：ROM存FSBL，Flash存SSBL和Firmware ========== *)
  Parameter DataFSBL DataSSBL DataFW : Data.
  Definition fsbl_blocks  := [{| block_data := DataFSBL; block_permission := ReadOnly |}].
  Definition ssbl_blocks  := [{| block_data := DataSSBL; block_permission := ReadWrite |}].
  Definition fw_blocks    := [{| block_data := DataFW; block_permission := ReadWrite |}].

  Parameter msg_SSBL msg_FW : Sig.Message.
  Definition sig_SSBL : Sig.Signature := Sig.sign Sig.privkey msg_SSBL.
  Definition sig_FW  : Sig.Signature := Sig.sign Sig.privkey msg_FW.

  (* 存储区起始地址与长度 *)
  Definition fsbl_addr := 0.
  Definition fsbl_len  := length fsbl_blocks.   (* = 1 *)
  Definition ssbl_addr := 0.
  Definition ssbl_len  := length ssbl_blocks.   (* = 1 *)
  Definition fw_addr   := ssbl_len.
  Definition fw_len    := length fw_blocks.     (* = 1 *)

  (* 初始化 ROM 和 Flash *)
  Definition initial_rom_storage : ROM_instance.StorageState :=
    ROM_instance.init_storage fsbl_blocks.

  Definition initial_flash_storage : Flash_instance.StorageState :=
    Flash_instance.init_storage (ssbl_blocks ++ fw_blocks).

  (* ========== 启动阶段与系统状态 ========== *)
  Inductive BootPhase := ROM_Phase | SSBL_Phase | Boot_Complete | Boot_Failed.
  Inductive SystemMode := SecureMode | ErrorMode.

  Record SystemState := {
    rom_state : ROM_instance.StorageState;
    flash_state : Flash_instance.StorageState;
    current_phase : BootPhase;
    system_mode : SystemMode;
    ssbl_verified : bool;
    firmware_verified : bool;
    boot_complete : bool
  }.

  Definition initial_state : SystemState := {|
    rom_state := initial_rom_storage;
    flash_state := initial_flash_storage;
    current_phase := ROM_Phase;
    system_mode := ErrorMode;
    ssbl_verified := false;
    firmware_verified := false;
    boot_complete := false
  |}.

  Definition ssbl_loaded (s:SystemState) : bool :=
    Nat.leb (ssbl_addr + ssbl_len) (Flash_instance.storage_size s.(flash_state)).

  Definition firmware_loaded (s:SystemState) : bool :=
    Nat.leb (fw_addr + fw_len) (Flash_instance.storage_size s.(flash_state)).

  Definition bootphase_eqb (p1 p2:BootPhase) : bool :=
    match p1,p2 with
    | ROM_Phase,ROM_Phase => true
    | SSBL_Phase,SSBL_Phase => true
    | Boot_Complete,Boot_Complete => true
    | Boot_Failed,Boot_Failed => true
    | _,_ => false
    end.

  (* ========== 启动流程：ROM 验证 SSBL -> SSBL 验证固件 ========== *)
  Definition fsbl_guard (s:SystemState) : bool :=
    bootphase_eqb s.(current_phase) ROM_Phase && ssbl_loaded s && Sig.verify Sig.pubkey msg_SSBL sig_SSBL.

  Definition fsbl_verify_ssbl (s:SystemState) : SystemState :=
    if fsbl_guard s then
      {| rom_state := s.(rom_state); flash_state := s.(flash_state); current_phase := SSBL_Phase;
         system_mode := s.(system_mode); ssbl_verified := true;
         firmware_verified := s.(firmware_verified); boot_complete := s.(boot_complete) |}
    else s.

  Definition fw_guard (s:SystemState) : bool :=
    s.(ssbl_verified) && bootphase_eqb s.(current_phase) SSBL_Phase && firmware_loaded s && Sig.verify Sig.pubkey msg_FW sig_FW.

  Definition ssbl_verify_firmware (s:SystemState) : SystemState :=
    if fw_guard s then
      {| rom_state := s.(rom_state); flash_state := s.(flash_state); current_phase := Boot_Complete;
         system_mode := SecureMode; ssbl_verified := s.(ssbl_verified);
         firmware_verified := true; boot_complete := true |}
    else s.

  Definition secure_boot_process (s:SystemState) : SystemState :=
    let s1 := fsbl_verify_ssbl s in
    ssbl_verify_firmware s1.

  (* ========== 安全谓词 ========== *)
  Definition is_secure_state (s:SystemState) : Prop :=
    s.(system_mode)=SecureMode /\
    s.(current_phase)=Boot_Complete /\
    s.(ssbl_verified)=true /\
    s.(firmware_verified)=true /\
    s.(boot_complete)=true /\
    ssbl_loaded s=true /\ firmware_loaded s=true.

  (* ========== 攻击建模：对Flash的任意写 ========== *)
  Definition attacker_write_ops := list Flash_instance.WriteOp.

  Definition attack_flash (ops:attacker_write_ops) (s:SystemState) : SystemState :=
    {| rom_state := s.(rom_state);
       flash_state := Flash_instance.apply_writes ops s.(flash_state);
       current_phase := s.(current_phase);
       system_mode := s.(system_mode);
       ssbl_verified := s.(ssbl_verified);
       firmware_verified := s.(firmware_verified);
       boot_complete := s.(boot_complete) |}.

  Lemma rom_attack_no_effect :
    forall ops s,
      {| rom_state := ROM_instance.apply_writes ops s.(rom_state);
         flash_state := s.(flash_state);
         current_phase := s.(current_phase);
         system_mode := s.(system_mode);
         ssbl_verified := s.(ssbl_verified);
         firmware_verified := s.(firmware_verified);
         boot_complete := s.(boot_complete) |}
      = s.
  Proof.
    intros ops s.
    destruct s; simpl.
    rewrite ROM_instance.apply_rom_writes_preserves_state.
    reflexivity.
  Qed.

  Lemma fsbl_guard_true : fsbl_guard initial_state = true.
  Proof.
    unfold fsbl_guard, initial_state, sig_SSBL; simpl.
    rewrite (Sig.verify_sign_correct msg_SSBL).
    unfold ssbl_loaded, ssbl_addr, ssbl_len, initial_flash_storage,
           Flash_instance.init_storage, ssbl_blocks, fw_blocks; simpl.
    reflexivity.
  Qed.

  Definition state_after_fsbl := fsbl_verify_ssbl initial_state.

  Lemma state_after_fsbl_shape :
    state_after_fsbl =
      {| rom_state := initial_rom_storage; flash_state := initial_flash_storage; current_phase := SSBL_Phase;
         system_mode := ErrorMode; ssbl_verified := true; firmware_verified := false; boot_complete := false |}.
  Proof.
    unfold state_after_fsbl, fsbl_verify_ssbl.
    rewrite fsbl_guard_true. reflexivity.
  Qed.

  Lemma fw_guard_true : fw_guard state_after_fsbl = true.
  Proof.
    rewrite state_after_fsbl_shape.
    unfold fw_guard, sig_FW; simpl.
    rewrite (Sig.verify_sign_correct msg_FW).
    unfold firmware_loaded, fw_addr, fw_len, initial_flash_storage,
           Flash_instance.init_storage, ssbl_blocks, fw_blocks; simpl.
    reflexivity.
  Qed.

  Theorem secure_boot_resists_rom_attack :
    forall ops,
      is_secure_state (secure_boot_process
                        {| rom_state := ROM_instance.apply_writes ops initial_rom_storage;
                            flash_state := initial_flash_storage;
                            current_phase := ROM_Phase;
                            system_mode := ErrorMode;
                            ssbl_verified := false;
                            firmware_verified := false;
                            boot_complete := false |}).
  Proof.
    intros ops.
  pose proof (ROM_instance.apply_rom_writes_preserves_state ops initial_rom_storage) as Hrom.
  unfold secure_boot_process, fsbl_verify_ssbl, ssbl_verify_firmware.
  replace (ROM_instance.apply_writes ops initial_rom_storage) with initial_rom_storage by (symmetry; exact Hrom).
  change ({| rom_state := initial_rom_storage; flash_state := initial_flash_storage; current_phase := ROM_Phase; system_mode := ErrorMode; ssbl_verified := false; firmware_verified := false; boot_complete := false |}) with initial_state.
  rewrite fsbl_guard_true.
  simpl.
  rewrite <- state_after_fsbl_shape.
  rewrite fw_guard_true.
  simpl.
  unfold is_secure_state; simpl; repeat split; reflexivity.
  Qed.

End MakeSecureBoot.
