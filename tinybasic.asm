; v0.2.2
;
; Bill O'Neill - Last update: 2011/11/11
;
; Monitor code is Open License and can be used freely
; Tiny Basic code is Copyright, Tom Pitman
;
; Consist of a minimal terminal monitor and Tom
; Pitman's Tiny Basic as a high-level
; programming language
;
; This code assembles as-is with the macro assembler in the
; Michal Kowalski simulator.
;
; It should be easy enough to configure this to run any-
; where in memory or convert it to assemble with any 6502
; assembler.
;
; Next steps:
;        More comments to document this code
;
;
; Revision History:
;
; v0.2.2q - 2017/08/12
;        Reverse engineering the code; added a lot of labels
;        and comments to the source code. Still a work in progress.
;
; v0.2.2p - 2017/07/25
;        Ported to Simple 65816 computer by TBW. Recoded so ACME
;        assembler can assemble it; changes made to I/O calls
;        and warm boot vector; and implement input line hook.
;        Also modified the startup code to avoid video memory
;        area. One difficulty: The BIOS's PRCH treats CR as if
;        it is a CR/LF sequence, which may play havoc with Tiny
;        Basic in its current form. We'll see...
;
; v0.2.2 - 2011/11/11
;        Reduced version containing only a terminal monitor
;        for a 6850 ACIA and Tom Pitman's Tiny Basic
;
; v0.2.1 - 2011/05/18
;        Ported to Michal Kowalski's macro assembler
;
; v0.2.0 - 2011/01/04
;        Corrected some label problems
;        Added/corrected some comments
;
; v0.1.3 - 2009/11/28
;        Changed the look-up table for the IL op-code
;          handlers to use labels instead of literal addresses
;          this helps make the code re-locatable.
;        Added some comments to source
;
; v0.1.2 - 2009/01/12
;        Added BREAK routine
;        Fixed my bad reference to error string " AT "
;        Compressed gaps in monitor code
;        Added some comments to source
;
; v0.1.1 - 2008/12/15
;        Initial working version
; 
;
; Notes:
;  - I changed the prompt character from a ":" ($3A) to a ">" ($3E) for no
;    other reason than I think it looks a bit better. The prompt character
;    is the second byte of the IL program table.
;
;  - This version is to run in Simple 65816. The memory map is as follows.
;
;    $0000-$CFFF     RAM (was: $0000-$7FFF)
;    $D000-$EFFF     Video RAM, I/O and microRAM area
;    ($F000-$F7FF     I/O - ACIA is at $F000 ... will be deleted)
;    $F000-$FBFF     ROM - Tiny Basic (was: $8000-$EFFF)
;    $FC00-$FFFF     ROM - Simple monitor
;
;  - Starting address in this version (referred to as "S" in the EXPERIMENTER'S
;    KIT) is $F000 (was: $8000)


;
; Tiny Basic starts here
;

; Zero page variables

LOWEST   =        $20               ; Lowest address of user program area
HIGHST   =        $22               ; Highest address of user program area
STACK    =        $24               ; End of user program area plus stack reserve
RETPTR   =        $26               ; Top of GOSUB stack
LINNUM   =        $28               ; Current line number of BASIC line

PGMPTR   =        $2A               ; Pointer to TBIL program table
TXTPTR   =        $2C               ; Pointer to program text area

INPLIN   =        $30               ; Input line buffer and computation stack ($30-$7F)
RNDNUM   =        $80               ; Random number generator workspace
VARS     =        $82               ; Variable "A" at $82-$83, "B" at $84-$85, etc. ($82-$B5)
TEMPS    =        $B6               ; Interpreter temporaries ($B6-$C7)

WORK     =        $BC               ; Working register (two byte pair)
RUNNIN   =        $BE               ; Running status flag

CSTOP    =        $C0               ; Computation stack pointer boundary variable
CSPTR    =        $C1               ; Computation stack pointer (points to $0030-$007F area)
                                    ; Note that CSPTR+1 is set to zero (in WARM_S routine) so that
                                    ;   (CSPTR) actually points to $0030-$007F stack area as well,
                                    ;   which is used in XCHBYT routine

TERMPOS  =        $BF               ; Terminal position

TXTBGN   =        $200              ; Start of available RAM area
ENDMEM   =        $E000             ; Barrier against video RAM area in Simple 65816

         * =      $F000             ; Start of Basic.  (was: $7600)
START

         JMP      FBLK              ; Jump to initialization code. So load address is start address.

CV       JMP      COLD_S            ; Cold start vector
WV       JMP      WARM_S            ; Warm start vector
IN_V     JMP      RCCHR             ; Input routine address. 
OUT_V    JMP      SNDCHR            ; Output routine address.
BV       JMP      CHKBREAK          ; Begin check break routine

;
; Some codes
;
BSC      !BYTE $5f                   ; Backspace code
LSC      !BYTE $18                   ; Line cancel code
PCC      !BYTE $80                   ; Pad character control
TMC      !BYTE $00                   ; Tape mode control
SSS      !BYTE $04                   ; Spare Stack size. (was $04 but documentation suggests $20)

;
; Code fragment for 'PEEK' and 'POKE'
;
PEEK     STX $C3                   ; 'PEEK' - store X in $C3
         BCC LBL008                ; On carry clear goto LBL008
         STX $C3                   ; 'POKE' - store X in $C3
         STA ($C2),Y               ; Store A in location pointed to by $C3 (hi) and Y (lo)
         RTS                       ; Return
LBL008   LDA ($C2),Y               ; Load A with value pointed to by $C3 (hi) and Y (lo)
         LDY #$00                  ; Reset Y
         RTS                       ; Return

;
; The following table contains the addresses for the ML handlers for the IL opcodes.
;
                                     ; ($30-$3F) (need to annotate that)
SRVT     !WORD  IL_BBR               ; ($40-$5F) Backward Branch Relative
         !WORD  IL_FBR               ; ($60-$7F) Forward Branch Relative
         !WORD  IL__BC               ; ($80-$9F) String Match Branch
         !WORD  IL__BV               ; ($A0-$BF) Branch if not Variable
         !WORD  IL__BN               ; ($C0-$DF) Branch if not a Number
         !WORD  IL__BE               ; ($E0-$FF) Branch if not End of line
         ; ($00-$07) opcodes are used for stack exchange; no addresses needed here
         !WORD  IL__NO               ; ($08) No Operation
         !WORD  IL__LB               ; ($09) Push Literal Byte onto Stack
         !WORD  IL__LN               ; ($0A) Push Literal Number
         !WORD  IL__DS               ; ($0B) Duplicate Top two bytes on Stack
         !WORD  IL__SP               ; ($0C) Stack Pop
         !WORD  IL__NO               ; ($0D) (Reserved)
         !WORD  IL__NO               ; ($0E) (Reserved)
         !WORD  IL__NO               ; ($0F) (Reserved)
         !WORD  IL__SB               ; ($10) Save Basic Pointer
         !WORD  IL__RB               ; ($11) Restore Basic Pointer
         !WORD  IL__FV               ; ($12) Fetch Variable
         !WORD  IL__SV               ; ($13) Store Variable
         !WORD  IL__GS               ; ($14) Save GOSUB line
         !WORD  IL__RS               ; ($15) Restore saved line
         !WORD  IL__GO               ; ($16) GOTO
         !WORD  IL__NE               ; ($17) Negate
         !WORD  IL__AD               ; ($18) Add
         !WORD  IL__SU               ; ($19) Subtract
         !WORD  IL__MP               ; ($1A) Multiply
         !WORD  IL__DV               ; ($1B) Divide
         !WORD  IL__CP               ; ($1C) Compare
         !WORD  IL__NX               ; ($1D) Next BASIC statement
         !WORD  IL__NO               ; ($1E) (Reserved)
         !WORD  IL__LS               ; ($1F) List the program
         !WORD  IL__PN               ; ($20) Print Number
         !WORD  IL__PQ               ; ($21) Print BASIC string
         !WORD  IL__PT               ; ($22) Print Tab
         !WORD  IL__NL               ; ($23) New Line
         !WORD  IL__PC               ; ($24) Print Literal String
         !WORD  IL__NO               ; ($25) (Reserved)
         !WORD  IL__NO               ; ($26) (Reserved)
         !WORD  IL__GL               ; ($27) Get input Line
         !WORD  ILRES1               ; ($28) (Seems to be reserved - No IL opcode calls this)
         !WORD  ILRES2               ; ($29) (Seems to be reserved - No IL opcode calls this)
         !WORD  IL__IL               ; ($2A) Insert BASIC Line
         !WORD  IL__MT               ; ($2B) Mark the BASIC program space Empty
         !WORD  IL__XQ               ; ($2C) Execute
         !WORD  WARM_S               ; ($2D) Stop (Warm Start)
         !WORD  IL__US               ; ($2E) Machine Language Subroutine Call
         !WORD  IL__RT               ; ($2F) IL subroutine return

ERRSTR   !RAW   " AT "               ; " AT " string used in error reporting.  Tom was right about this.
         !RAW   $80                  ; String terminator

PGMADR   !WORD  ILTBL                ; Address of IL program table

;
; Begin Cold Start
;
; Load start of free ram (TXTBGN; was: $0200) into LOWEST
; and initialize the address for end of free ram (HIGHST)
;
COLD_S   lda #<TXTBGN               ; Load accumulator with TXTBGN
         sta LOWEST                 ; Store $00 in $20
         sta HIGHST                 ; Store $00 in $22
         lda #>TXTBGN               ; Load accumulator with TXTBGN
         sta LOWEST+1               ; Store TXTBGN in $21
         sta HIGHST+1               ; Store TXTBGN in $23
;
;
; Begin test for free RAM
;

         ldy #1                     ; Load register Y with 1
MEM_T    lda (HIGHST),Y             ; Load accumulator With the contents of a byte of memory
         tax                        ; Save it to X
         eor #$FF                   ; Next 4 instuctions test to see if this memory location
         sta (HIGHST),Y             ;   is RAM by trying to write something new to it - new value
         cmp (HIGHST),Y             ;   gets created by XORing the old value with $FF - store the
         php                        ;   result of the test on the stack to look at later
         txa                        ; Retrieve the old memory value
         sta (HIGHST),Y             ; Put it back where it came from
         inc HIGHST                 ; Increment HIGHST (for next memory location)
         bne SKP_PI                 ; Skip if we don't need to increment page
         inc HIGHST+1               ; Increment HIGHST+1 (for next memory page)
SKP_PI   lda HIGHST+1               ; Get high byte of memory address
         cmp #>ENDMEM               ; Did we reach start address of Tiny Basic?
         bne PULL                   ; Branch if not
         lda HIGHST                 ; Get low byte of memory address
         cmp #<ENDMEM               ; Did we reach start address of Tiny Basic?
         beq TOP                    ; If so, stop memory test so we don't overwrite ourselves
PULL
         plp                        ; Now look at the result of the memory test
         beq MEM_T                  ; Go test the next memory location if the last one was RAM
TOP
         dey                        ; If last memory location did not test as RAM, decrement Y (should be zero now)
;
; TBIL MT (Mark the BASIC program space Empty)
;
IL__MT   cld                        ; Make sure we're not in decimal mode
         lda LOWEST                 ; Load up the low order byte of the start of free ram
         adc SSS                    ; Add to the spare stack size
         sta $24                    ; Store the result in $0024
         tya                        ; Y is zero
         adc LOWEST+1               ; And add it to the high order byte of the start of free RAM
         sta $25                    ; Store the result in $0025
         tya                        ; Retrieve Y again
         sta (LOWEST),Y             ; Store A in the first byte of program memory
         iny                        ; Increment Y
         sta (LOWEST),Y             ; Store A in the second byte of program memory
;
; Begin Warm Start
;
WARM_S   lda HIGHST                 ; Set $C6 and RETPTR to HIGHST
         sta $C6
         sta RETPTR
         lda HIGHST+1
         sta $C7
         sta RETPTR+1
         jsr P_NWLN                 ; Go print CR, LF and pad characters
;
; Restart the interpreter state
;
RESTRT   lda PGMADR                 ; Reset the start of the IL Table
         sta PGMPTR                 ;   by setting PGMPTR to PGMADR
         lda PGMADR+1               ;
         sta PGMPTR+1
         lda #$80                   ; Reset the computation stack pointer
         sta CSPTR                  ;   to bottom
         lda #$30
         sta CSTOP                  ; Set computation stack top boundary to $30
         ldx #$00                   ; Set RUNNIN to zero
         stx RUNNIN
         stx CSPTR+1                ; CSPTR+1 is permanently set to zero
         dex
         txs                        ; Reset system stack pointer to $FF (bottom)

;
; IL execution loop
;
.loop    cld                        ; Make sure we're in binary mode 
         jsr PGMBYT                 ; Go read a byte from the IL program table
         jsr EXECUT                 ; Go decide what to do with it
         jmp .loop                  ; Repeat
;
;
;
         !BYTE $83                  ; No idea about this
         !BYTE $65                  ; No idea about this
;
;
; Routine to service the TBIL Instructions
;
EXECUT   cmp #$30                   ;
         bcs LBL011                 ; If it's $30 or higher, it's a Branch or Jump - go handle it
         cmp #$08                   ; 
         bcc XCHBYT                 ; If it's less than $08, it's a stack exchange - go handle it
         asl                        ; Multiply the OP code by 2 
         tax                        ;   and make it an index
EXEC     lda SRVT-$03,X             ; Get the high byte of the OP Code handling routine
         pha                        ;   and save it on the stack
         lda SRVT-$04,X             ; Get the low byte
         pha                        ;   and save it on the stack
         php                        ; Save the processor status too
         rti                        ; Now go execute the OP Code handling routine
;
;
; Routine to handle the stack exchange
; Exchange the low byte of TOS with the low byte of CSPTR+n,
;   where n is passed in accumulator
;
XCHBYT   adc CSPTR                  ; Add index number (should be even number) to
         tax                        ;   CSPTR so that it points to CSPTR+n
         lda (CSPTR),Y              ; Get low byte of TOS
         pha
         lda $00,X                  ; Get low byte of CSPTR+n and
         sta (CSPTR),Y              ;   write into low byte of TOS
         pla
         sta $00,X                  ; Write original low byte of TOS into
         rts                        ;   low byte of CSPTR+n and exit
;
; Print error message?
;
PRERR    jsr P_NWLN                 ; Go print CR, LF and pad characters
         lda #'!'                   ; '!' character
         jsr OUT_V                  ; Go print it
         lda PGMPTR                 ; Load the current TBIL pointer (low) 
         sec                        ; Set the carry flag
         sbc PGMADR                 ; Subtract the TBIL table origin (low)
         tax                        ; Move the difference to X
         lda PGMPTR+1               ; Load the current TBIL pointer (high)
         sbc PGMADR+1               ; Subtract the TBIL table origin (high)
         jsr PRAXNM
         lda RUNNIN                 ; Was the program in running state?
         beq .serr                  ; No, just a simple error (bell)
         lda #<ERRSTR               ; Get low byte of error string address
         sta PGMPTR                 ; Put in PGMPTR
         lda #>ERRSTR               ; Get high byte of error string address
         sta PGMPTR+1               ; Put in PGMPTR+1
         jsr IL__PC                 ; Go report an error has been detected
         ldx LINNUM                 ; Print the current line number
         lda LINNUM+1
         jsr PRAXNM
.serr    lda #$07                   ; ASCII Bell
         jsr OUT_V                  ; Go ring Bell
         jsr P_NWLN                 ; Go print CR, LF and pad characters
CLRSTK   lda RETPTR                 ; Set $C6 to RETPTR
         sta $C6
         lda RETPTR+1
         sta $C7
         jmp RESTRT
;
; Pop computation stack pointer
;
POPNBR   ldx #$7C                   ; Does the computation stack have at
POPNB1   cpx CSPTR                  ;   least two items (four bytes)?
PRERR1   bcc PRERR                  ; No, error
         ldx CSPTR                  ; Load old computation stack pointer
         inc CSPTR                  ;   into X and increment computation
         inc CSPTR                  ;   stack pointer by two
         clc                        ; Carry cleared for use by math routines
         rts
;
; TBIL Backward Branch Relative
;
IL_BBR   dec WORK+1                 ; Entry point for
;
; TBIL Forward Branch Relative
;
IL_FBR   lda WORK+1                 ; Entry point for
         beq PRERR
LBL017   lda WORK                   ; Set PGMPTR to WORK
         sta PGMPTR
         lda WORK+1
         sta PGMPTR+1
         rts
;
; Jump handling routine
;
LBL011   cmp #$40
         bcs LBL016                 ; If it's not a Jump, go to branch handler
         pha
         jsr PGMBYT                 ; Go read a byte from the TBIL table
         adc PGMADR
         sta WORK
         pla
         pha
         and #$07
         adc PGMADR+1
         sta WORK+1
         pla
         and #$08
         bne LBL017
         lda WORK                   ; Swap WORK and PGMPTR
         ldx PGMPTR
         sta PGMPTR
         stx WORK
         lda WORK+1
         ldx PGMPTR+1
         sta PGMPTR+1
         stx WORK+1
LBL126   lda $C6                    ; Decrement $C6 by 1
         sbc #$01
         sta $C6
         bcs .skip
         dec $C7
.skip    cmp $24                    ; Is $C6 < $24?
         lda $C7
         sbc $25
         bcc PRERR1                 ; Yes, error (go to PRERR)
         lda WORK
         sta ($C6),Y
         iny
         lda WORK+1
         sta ($C6),Y
         rts
;
;
; Branch Handler
;
LBL016   pha
         lsr
         lsr
         lsr
         lsr
         and #$0E
         tax
         pla
         cmp #$60                   ; Is it a forward branch IL code?
         and #$1F
         bcs LBL020                 ; Yes, go and add its offset
         ora #$E0                   ; Create a negative offset
LBL020   clc
         beq LBL021                 ; Offset is zero, so skip the addition
         adc PGMPTR                 ; Add offset to PGMPTR and save to WORK
         sta WORK
         tya
         adc PGMPTR+1
LBL021   sta WORK+1
         jmp EXEC                   ; And go to IL table dispatcher
;
; TBIL BC (String Match Branch)
;
IL__BC   lda TXTPTR                 ; Save TXTPTR into $B8
         sta $B8
         lda TXTPTR+1
         sta $B9
.match   jsr CHRGOT
         jsr CHRGET
         eor (PGMPTR),Y             ; Test for char match and end of
         tax                        ;   string (high bit), then save it
         jsr PGMBYT                 ; Go read a byte from the TBIL table
         txa                        ; Is it a plain match?
         beq .match                 ; Yes, continue checking for a match
         asl                        ; Mask out high bit, then is it a final match?
         beq BCEXIT                 ; Yes, exit
         lda $B8                    ; Restore TXTPTR from $B8
         sta TXTPTR
         lda $B9
         sta TXTPTR+1
DO_FBR   jmp IL_FBR                 ; Match failed, so do a (forward) branch
;
; TBIL BE (Branch if not End of line)
;
IL__BE   jsr CHRGOT                 ; Check that CR is there
         cmp #$0D
         bne DO_FBR                 ; Else do a (forward) branch
BCEXIT   rts
;
; TBIL BV (Branch if not Variable)
;
IL__BV   jsr CHRGOT                 ; Get current char from program area
         cmp #'Z'+1                 ; Is it a letter ('A' to 'Z')?
         bcs DO_FBR                 ; No, do a (forward) branch
         cmp #'A'
         bcc DO_FBR                 ; No, do a (forward) branch
         asl                        ; Yes, so create an index out of it
         jsr PSHACC                 ;   and push it on stack
CHRGET   ldy #$00
         lda (TXTPTR),Y             ; Get a char from program text
         inc TXTPTR                 ;   and increment TXTPTR by one
         bne .chk
         inc TXTPTR+1
.chk     cmp #$0D                   ; CR?
         clc
         rts
;
; CHRGOT - Starting with current character in the program area, skip
;          any blanks until a nonblank character is reached, and return
;          with carry clear (nondigit) or set (digit)
;
chgot1   jsr CHRGET
CHRGOT   lda (TXTPTR),Y             ; Get a char from program text
         cmp #' '                   ; Space?
         beq chgot1                 ; Yes, skip it
         cmp #':'                   ; Colon?
         clc
         bpl .exit                  ; Yes, exit with carry flag clear
         cmp #'0'                   ; Digit char? (carry set if yes)
.exit    rts
;
; TBIL BN (Branch if not a Number)
;
IL__BN   jsr CHRGOT                 ; Get current char from program area
         bcc DO_FBR                 ; Not a digit, so do a (forward) branch
         sty WORK                   ; Set WORK to zero
         sty WORK+1
.loop1   lda WORK                   ; Set WORK to 10*WORK
         ldx WORK+1
         asl WORK
         rol WORK+1
         asl WORK
         rol WORK+1
         clc
         adc WORK
         sta WORK
         txa
         adc WORK+1
         asl WORK
         rol
         sta WORK+1
         jsr CHRGET                  ; Get next char from program area
         and #$0F                    ; Assuming it is a digit, get the value
         adc WORK                    ;   and add it to WORK
         sta WORK
         tya
         adc WORK+1
         sta WORK+1
         jsr CHRGOT                  ; Get the same char again
         bcs .loop1                  ; It is a digit, so continue adding it to WORK
         jmp PSHWRK
;
; Find BASIC line with target line number
;
FINDLN   jsr IL__SP                 ; Pop the number into WORK
         lda WORK                   ; Is WORK zero?
         ora WORK+1
         beq PQERR                  ; Yes, print error
FNDLN1   lda LOWEST                 ; Set TXTPTR to LOWEST
         sta TXTPTR
         lda LOWEST+1
         sta TXTPTR+1
LBL040   jsr GETNUM
         beq LBL038
         lda LINNUM                 ; Is LINNUM >= WORK?
         cmp WORK
         lda LINNUM+1
         sbc WORK+1
         bcs LBL038                 ; Yes, ...
.skip5   jsr CHRGET                 ; Skip the BASIC program line
         bne .skip5                 ;   by searching for $00 sentinel
         jmp LBL040                 ; Continue looking for ...
LBL038   lda LINNUM                 ; Test whether LINNUM = WORK
         eor WORK
         bne .skip6
         lda LINNUM+1
         eor WORK+1
.skip6   rts
;
; TBIL PC (Print Literal String)
;
pcloop   jsr CPRCHR
IL__PC   jsr PGMBYT                 ; Go read a byte from the TBIL table
         bpl pcloop                 ; ...else fall thru to ...
;
; Counted printing a character
;
CPRCHR   inc TERMPOS                ; Update terminal position
         bmi .nopr                  ; 127 is maximum allowed; won't print beyond that
         jmp OUT_V                  ; Go print it
.nopr    dec TERMPOS                ; Keep TERMPOS at its maximum
prexit   rts
;
;
;
LBL046   cmp #'"'                   ; Is it a quote?
         beq prexit                 ; No, quit
         jsr CPRCHR
;
; TBIL PQ (Print BASIC string)
;
IL__PQ   jsr CHRGET                 ; Entry point for
         bne LBL046
PQERR    jmp PRERR
;
; TBIL PT (Print Tab)
;
IL__PT   lda #' '                   ; Print a space
         jsr CPRCHR
         lda TERMPOS
         and #$87                   ; Do a modulo of 8, plus see if it it has gone past 127
         bmi prexit                 ; Yes, it went past 127, so quit
         bne IL__PT                 ; It is not divisible by 8, so continue printing spaces
         rts                        ; Else it's all done
;
; TBIL CP (Compare)
;
IL__CP   ldx #$7B                   ; Make sure the computation stack has
         jsr POPNB1                 ;   at least 5 bytes, then decrement
         inc CSPTR                  ;   CSPTR by 5 bytes (POPNB1 already
         inc CSPTR                  ;   decremented it by 2)
         inc CSPTR
         sec                        ; Subtract TOS from $03 and store into TOS
         lda $03,X
         sbc $00,X
         sta $00,X
         lda $04,X
         sbc $01,X
         bvc LBL052                 ; No overflow
         eor #$80                   ; No idea what it does
         ora #$01
LBL052   bmi LBL053                 ; It's negative, so that means TOS < $03
         bne LBL054
         ora $00,X
         beq LBL049
LBL054   lsr $02,X
LBL049   lsr $02,X
LBL053   lsr $02,X
         bcc LBL050
PGMBYT   ldy #$00                   ; Read a byte from the TBIL Table
         lda (PGMPTR),Y             ;
         inc PGMPTR                 ; Increment TBIL Table pointer as required
         bne .skip0                 ;
         inc PGMPTR+1               ;
.skip0   ora #$00                   ; Check for $00 and set the 'Z' flag acordingly
LBL050   rts                        ; Return
;
; TBIL NX (Next BASIC statement)
;
IL__NX   lda RUNNIN                 ; Is the program running?
         beq QUIT                   ; No, go to inputting
.skip7   jsr CHRGET                 ; Skip rest of BASIC statement until it hits $00
         bne .skip7
         jsr GETNUM                 ; Get BASIC line number
         beq RPERR                  ; It's zero, so error
DOSTMT   jsr LBL058                 ; Set RUNNIN to 1
         jsr BV                     ; Test for break
         bcs RESETP                 ; Break invoked, so quit running
         lda $C4                    ; Set PGMPTR to $C4
         sta PGMPTR
         lda $C5
         sta PGMPTR+1
         rts
;
; Reset IL program pointer and go to error
;
RESETP   lda PGMADR                 ; Reset PGMPTR back to the beginning of
         sta PGMPTR                 ;   the IL program table (PGMADR)
         lda PGMADR+1
         sta PGMPTR+1
RPERR    jmp PRERR                  ; And go to error
;
;
;
QUIT     sta TERMPOS                ; Set TERMPOS to zero,
         jmp CLRSTK                 ;   clear stack and resume inputting
;
; TBIL XQ (Execute)
;
IL__XQ   lda LOWEST                 ; Set TXTPTR to LOWEST
         sta TXTPTR
         lda LOWEST+1
         sta TXTPTR+1
         jsr GETNUM                 ; Get line number
         beq RPERR                  ; Error if it's zero
         lda PGMPTR                 ; Set $C4 to PGMPTR
         sta $C4
         lda PGMPTR+1
         sta $C5
LBL058   lda #$01                   ; Set RUNNIN to 1
         sta RUNNIN
         rts
;
; TBIL GO (GOTO)
;
IL__GO   jsr FINDLN                 ; Find BASIC line with target line number
         beq DOSTMT                 ; Found; execute it
GOERR    lda WORK                   ; Otherwise set LINNUM to WORK
         sta LINNUM
         lda WORK+1
         sta LINNUM+1
         jmp PRERR                  ;   and print error
;
; TBIL RS (Restore saved line)
;
IL__RS   jsr LBL063                 ; Entry point for
         jsr LBL064
         jsr FNDLN1
         bne GOERR
         rts
;
; Read line number into LINNUM
;
GETNUM   jsr CHRGET                 ; Read next two bytes in program area
         sta LINNUM                 ;   into LINNUM, and return with zero flag
         jsr CHRGET                 ;   set according to whether LINNUM is zero
         sta LINNUM+1
         ora LINNUM
         rts
;
; TBIL DS (Duplicate Top two bytes on Stack)
;
IL__DS   jsr IL__SP                 ; Pop TOS onto WORK then push WORK twice
         jsr PSHWRK
PSHWRK   lda WORK+1                 ; Push WORK onto computation stack
PSHWKA   jsr PSHACC                 ; Push WORK(low)/Accum(high) onto
         lda WORK                   ;   computation stack
PSHACC   ldx CSPTR                  ; Push accumulator onto computation
         dex                        ;   stack
         sta $00,X
         stx CSPTR                  ; Update computation stack pointer
         cpx CSTOP                  ; Has it hit the top boundary of
         bne IL__NO                 ;   computation stack area? No
LBL068   jmp PRERR                  ; Error: computation stack overflow
;
; Pop a byte from computation stack
;
POPBYT   ldx CSPTR                  ; Load computation stack pointer
         cpx #$80                   ; Is the stack empty?
         bpl LBL068                 ; Yes, error
         lda $00,X                  ; Pop a byte from the stack
         inc CSPTR                  ;   and update the pointer
;
; TBIL NO (No Operation)
;
IL__NO   rts                        ; Just that...no operation :-)
;
; Print acc/X as (unsigned) number
;
PRAXNM   sta WORK+1                 ; Copy accumulator and X register
         stx WORK                   ;   to WORK
         jmp PRNUM                  ; Go print (unsigned) number
;
; TBIL PN (Print Number)
;
IL__PN   ldx CSPTR                  ; Load computation stack pointer
         lda $01,X                  ; See whether the number is
         bpl .skip1                 ;   negative...no, skip it
         jsr IL__NE                 ; Else negate the number on stack
         lda #'-'                   ; Print a '-' to show minus sign
         jsr CPRCHR
.skip1   jsr IL__SP
PRNUM    lda #$1F
         sta $B8
         sta $BA
         lda #$2A
         sta $B9
         sta $BB
         ldx WORK
         ldy WORK+1
         sec
.sub10k  inc $B8
         txa                        ; Subtract 10000 ($2710) from Y/X register pair
         sbc #$10
         tax
         tya
         sbc #$27
         tay
         bcs .sub10k
.add1k   dec $B9
         txa                        ; Add 1000 ($03E8) to Y/X register pair
         adc #$E8
         tax
         tya
         adc #$03
         tay
         bcc .add1k
         txa
.sub100  sec                        ; Subtract 100 ($64) from accumulator
         inc $BA
         sbc #$64
         bcs .sub100
         dey
         bpl .sub100
.add10   dec $BB                    ; Add 10 ($0A) to accumulator
         adc #$0A
         bcc .add10
         ora #$30                   ; Convert it to ASCII digit
         sta WORK
         lda #$20
         sta WORK+1
         ldx #$FB
LBL199   stx $C3
         lda WORK+1,X
         ora WORK+1
         cmp #$20
         beq LBL076
         ldy #$30
         sty WORK+1
         ora WORK+1
         jsr CPRCHR
LBL076   ldx $C3
         inx
         bne LBL199
         rts
;
; TBIL LS (List the program)
;
IL__LS   lda TXTPTR+1               ; Save TXTPTR on system stack
         pha
         lda TXTPTR
         pha
         lda LOWEST                 ; Set TXTPTR to LOWEST
         sta TXTPTR
         lda LOWEST+1
         sta TXTPTR+1
         lda $24
         ldx $25
         jsr LBL077
         beq LBL078
         jsr LBL077
LBL078   lda TXTPTR                 ; Is TXTPTR >= $B6?
         sec
         sbc $B6
         lda TXTPTR+1
         sbc $B7
         bcs LBL079                 ; Yes, exiting
         jsr GETNUM
         beq LBL079                 ; Reach the end of program area, exiting
         ldx LINNUM                 ; Print line number and ...
         lda LINNUM+1
         jsr PRAXNM
         lda #' '                   ;   a blank after that number
LBL080   jsr CPRCHR
         jsr BV                     ; Test for break
         bcs LBL079                 ; Break hit, so exiting
         jsr CHRGET                 ; Get a char from program area
         bne LBL080                 ;   and print it until it hits a $00
         jsr IL__NL                 ; Print a new line
         jmp LBL078                 ; Loop back to LIST
;
;
;
LBL077   sta $B6
         inc $B6
         bne LBL082
         inx
LBL082   stx $B7
         ldy CSPTR                  ; Load computation stack pointer
         cpy #$80
         beq LBL083
         jsr FINDLN                 ; Find BASIC line with target line number
;
;
;
LBL099   lda TXTPTR                 ; Decrement TXTPTR by 2
         ldx TXTPTR+1
         sec
         sbc #$02
         bcs .skip2
         dex
.skip2   sta TXTPTR
         jmp LBL085                 ;
LBL079   pla                        ; Restore TXTPTR from system stack
         sta TXTPTR
         pla
         sta TXTPTR+1
LBL083   rts
;
; TBIL NL (New Line)
;
IL__NL   lda TERMPOS                ; Is the terminal position past 127?
         bmi LBL083                 ; Yes, exit. Otherwise fall thru to ...
;
; Routine to print a new line.  It handles CR, LF
; and adds pad characters to the ouput
;
P_NWLN   lda #$0D                   ; Load up a CR
         jsr OUT_V                  ; Go print it
         lda PCC                    ; Load the pad character code
         and #$7F                   ; Test to see - 
         sta TERMPOS                ;   how many pad characters to print
         beq .prlf                  ; Skip if 0
.prpad   jsr LBL087                 ; Go print pad character
         dec TERMPOS                ; One less
         bne .prpad                 ; Loop until 0
.prlf    lda #$0A                   ; Load up a LF
         jmp LBL089                 ; Go print it
;
;
;
LBL092   ldy TMC
LBL091   sty TERMPOS
         bcs LBL090
;
; TBIL GL (Get input Line)
;
IL__GL   lda #$30                   ; Set TXTPTR and CSTOP to $0030
         sta TXTPTR
         sta CSTOP
         sty TXTPTR+1
         jsr PSHWRK
LBL090   eor $80
         sta $80
         jsr IN_V
         ldy #$00
         ldx CSTOP
         and #$7F
         beq LBL090                 ; It is a NUL
         cmp #$7F                   ; Is it a rubout?
         beq LBL090
         cmp #$13                   ; Is it a ...?
         beq LBL091
         cmp #$0A                   ; Is it a line feed?
         beq LBL092
         cmp LSC                    ; Is it a line cancel?
         beq .cancl
         cmp BSC                    ; Is it a backspace?
         bne .back
         cpx #$30                   ; Has it reached the end of input buffer?
         bne LBL095                 ; No, ...
.cancl   ldx TXTPTR
         sty TERMPOS                ; Reset TERMPOS to zero
         lda #$0D
.back    cpx CSPTR                  ; ... computation stack pointer
         bmi LBL096
         lda #$07                   ; ASCII Bell
         jsr CPRCHR                 ; Ring the bell
         jmp LBL090
LBL096   sta $00,X                  ; Append a char to the buffer
         inx
         inx
LBL095   dex
         stx CSTOP                  ; Set CSTOP to current buffer position
         cmp #$0D                   ; Is it a CR?
         bne LBL090                 ; No, continue inputting
         jsr IL__NL                 ; Print a new line and ...
;
; TBIL SP (Stack Pop)
;
IL__SP   jsr POPBYT                 ; Pop value from computation
         sta WORK                   ;   stack onto WORK
         jsr POPBYT
         sta WORK+1
         rts
;
; TBIL IL (Insert BASIC Line)
;
IL__IL   jsr LBL098                 ; Entry point for
         jsr FINDLN                 ; Find BASIC line with target line number
         php
         jsr LBL099
         sta $B8                    ; Set $B8 to TXTPTR
         stx $B9
         lda WORK                   ; Set $B6 to WORK
         sta $B6
         lda WORK+1
         sta $B7
         ldx #$00
         plp
         bne LBL100
         jsr GETNUM
         dex
         dex
LBL101   dex
         jsr CHRGET
         bne LBL101
LBL100   sty LINNUM
         sty LINNUM+1
         jsr LBL098
         lda #$0D
         cmp (TXTPTR),Y
         beq LBL102
         inx
         inx
         inx
LBL103   inx
         iny
         cmp (TXTPTR),Y
         bne LBL103
         lda $B6                    ; Set LINNUM to $B6
         sta LINNUM
         lda $B7
         sta LINNUM+1
LBL102   lda $B8                    ; Set WORK to $B8
         sta WORK
         lda $B9
         sta WORK+1
         clc
         ldy #$00
         txa
         beq LBL104
         bpl LBL105
         adc $2E
         sta $B8
         lda $2F
         sbc #$00
         sta $B9
LBL109   lda ($2E),Y
         sta ($B8),Y
         ldx $2E
         cpx $24
         bne LBL106
         lda $2F
         cmp $25
         beq LBL107
LBL106   inx
         stx $2E
         bne LBL108
         inc $2F
LBL108   inc $B8
         bne LBL109
         inc $B9
         bne LBL109
LBL105   adc $24
         sta $B8
         sta $2E
         tya
         adc $25
         sta $B9
         sta $2F
         lda $2E
         sbc $C6
         lda $2F
         sbc $C7
         bcc LBL110
         dec PGMPTR
         jmp PRERR
LBL110   lda ($24),Y
         sta ($2E),Y
         ldx $24                    ; Decrement $24 by 1
         bne LBL111
         dec $25
LBL111   dec $24
         ldx $2E                    ; Decrement $2E by 1
         bne LBL112
         dec $2F
LBL112   dex
         stx $2E
         cpx WORK                   ; Is $2E = WORK?
         bne LBL110                 ; No, go to ...
         ldx $2F
         cpx WORK+1
         bne LBL110                 ; No, go to ...
LBL107   lda $B8                    ; Set $24 to $B8
         sta $24
         lda $B9
         sta $25
LBL104   lda LINNUM                 ; Is LINNUM zero?
         ora LINNUM+1
         beq LBL113                 ; Yes, ...
         lda LINNUM                 ; Else write LINNUM to (WORK)
         sta (WORK),Y
         iny
         lda LINNUM+1
         sta (WORK),Y
LBL114   iny
         sty $B6
         jsr CHRGET
         php
         ldy $B6
         sta (WORK),Y
         plp
         bne LBL114
LBL113   jmp RESTRT
;
; TBIL DV (Divide)
;
IL__DV   jsr POPNBR                 ; Entry point for
         lda $03,X
         and #$80
         beq LBL116
         lda #$FF
LBL116   sta WORK
         sta WORK+1
         pha
         adc $02,X
         sta $02,X
         pla
         pha
         adc $03,X
         sta $03,X
         pla
         eor $01,X
         sta $BB
         bpl LBL117
         jsr LBL118
LBL117   ldy #$11
         lda $00,X
         ora $01,X
         bne LBL119
         jmp PRERR
LBL119   sec
         lda WORK
         sbc $00,X
         pha
         lda WORK+1
         sbc $01,X
         pha
         eor WORK+1
         bmi LBL120
         pla
         sta WORK+1
         pla
         sta WORK
         sec
         jmp LBL121
LBL120   pla
         pla
         clc
LBL121   rol $02,X
         rol $03,X
         rol WORK
         rol WORK+1
         dey
         bne LBL119
         lda $BB
         bpl LBL122
;
; TBIL NE (Negate)
;
IL__NE   ldx CSPTR                  ; Load computation stack pointer
LBL118   sec                        ; Negates the TOS by subtracting
         tya                        ;   it from zero (Y is zero) and
         sbc $00,X                  ;   replacing TOS with it
         sta $00,X
         tya
         sbc $01,X
         sta $01,X
LBL122   rts
;
; TBIL SU (Subtract)
;
IL__SU   jsr IL__NE                 ; Negate the TOS and falls thru to...
;
; TBIL AD (Add)
;
IL__AD   jsr POPNBR                 ; Add TOS to NOS and NOS becomes TOS
         lda $00,X
         adc $02,X
         sta $02,X
         lda $01,X
         adc $03,X
         sta $03,X
         rts
;
; TBIL MP (Multiply)
;
IL__MP   jsr POPNBR
         ldy #$10                   ; Loop 16 times
         lda $02,X                  ; Copy NOS to WORK
         sta WORK
         lda $03,X
         sta WORK+1
.mult    asl $02,X                  ; Shift WORK/NOS unit left by 1
         rol $03,X
         rol WORK
         rol WORK+1
         bcc .skip3
         clc                        ; Add TOS to NOS
         lda $02,X
         adc $00,X
         sta $02,X
         lda $03,X
         adc $01,X
         sta $03,X
.skip3   dey
         bne .mult
         rts
;
; TBIL FV (Fetch Variable)
;
IL__FV   jsr POPBYT                 ; Pop a variable index into X
         tax
         lda $00,X
         ldy $01,X
         dec CSPTR
         ldx CSPTR
         sty $00,X
         jmp PSHACC
;
; TBIL SV (Store Variable)
;
IL__SV   ldx #$7D                   ; Make sure the computation stack
         jsr POPNB1                 ;   has at least three bytes on it
         lda $01,X                  ; Pop value and stask it on system stack
         pha
         lda $00,X
         pha
         jsr POPBYT                 ; Pop a variable index into X
         tax
         pla                        ; Retrieve saved value and write it
         sta $00,X                  ;   into variable pointed to by X
         pla
         sta $01,X
         rts
;
; TBIL RT (IL subroutine return)
;
IL__RT   jsr LBL063                 ; Entry point for
         lda WORK                   ; Set PGMPTR to WORK
         sta PGMPTR
         lda WORK+1
         sta PGMPTR+1
         rts
;
; TBIL SB (Save Basic Pointer)
;
IL__SB   ldx #$2C                   ; Entry point for
         bne LBL125                 ; go to common routine
;
; TBIL RB (Restore Basic Pointer)
;
IL__RB   ldx #$2E                   ; Entry point for
LBL125   lda $00,X
         cmp #$80
         bcs LBL098
         lda $01,X
         bne LBL098
         lda TXTPTR                 ; Set $2E to TXTPTR
         sta $2E
         lda TXTPTR+1
         sta $2F
         rts
;
; Swap TXTPTR and $2E
;
LBL098   lda TXTPTR                 ; Swap TXTPTR and $2E
         ldy $2E
         sty TXTPTR
         sta $2E
         lda TXTPTR+1
         ldy $2F
         sty TXTPTR+1
         sta $2F
         ldy #$00
         rts
;
; TBIL GS (Save GOSUB line)
;
IL__GS   lda LINNUM                 ; Set WORK to LINNUM
         sta WORK
         lda LINNUM+1
         sta WORK+1
         jsr LBL126
         lda $C6                    ; Set RETPTR to $C6
         sta RETPTR
         lda $C7
LBL064   sta RETPTR+1
LBL129   rts
;
;
;
LBL063   lda ($C6),Y                ; Set WORK to ($C6)
         sta WORK
         jsr .check
         lda ($C6),Y
         sta WORK+1
.check   inc $C6                    ; Increment $C6 by 1
         bne .skip4
         inc $C7
.skip4   lda HIGHST                 ; Is HIGHST < $C6?
         cmp $C6
         lda HIGHST+1
         sbc $C7
         bcs LBL129                 ; No, exit
         jmp PRERR                  ; Error
;
; TBIL US (Machine Language Subroutine Call)
;
IL__US   jsr .dousr                 ; Execute USR() function, then
         sta WORK                   ;   push the accumulator onto
         tya                        ;   the computation stack
         jmp PSHWKA
.dousr   jsr IL__SP                 ; Copy low byte of third argument
         lda WORK                   ;   ("A" register value) to $B6
         sta $B6
         jsr IL__SP                 ; Copy high byte of second argument
         lda WORK+1                 ;   ("X" register value) to $B7
         sta $B7
         ldy WORK
         jsr IL__SP                 ; Copy first argument (machine
         ldx $B7                    ;   code address) to WORK
         lda $B6                    ; Load accumulator and X register with values
         clc
         jmp (WORK)                 ; Invoke the machine routine
;
; TBIL LN (Push Literal Number)
;
IL__LN   jsr IL__LB                 ; Read two bytes from the IL program table and push it
;
; TBIL LB (Push Literal Byte onto Stack) - Go read a byte from the IL table
;
IL__LB   jsr PGMBYT                 ; Read a byte from the IL program table
         jmp PSHACC                 ;   and push it on stack
LBL085   stx TXTPTR+1
         cpx #$00
         rts
;
;
;
ILRES2   ldy #$02                   ; These two entry points are for code that
ILRES1   sty WORK                   ;  does not seem to get called.  Need more research.
         ldy #$29                   ; My analysis: Set WORK to $2902, fetch a
         sty WORK+1                 ;   byte from it and if it is $08, go to
         ldy #$00                   ;   some code inside IL__DV (Divide) routine...?!?
         lda (WORK),Y               ; Why this code? Beats me
         cmp #$08
         bne LBL133
         jmp LBL117
LBL133   rts
;
; Subroutine to decide which pad characters to print
;
LBL089   jsr OUT_V                  ; Entry point with a character to print first
LBL087   lda #$FF                   ; Normal entry point - Set pad to $FF
         bit PCC                    ; Check if the pad flag is on
         bmi LBL134                 ; Skip it if not
         lda #$00                   ; set pad to $00
LBL134   jmp OUT_V                  ; Go print it


;
; TBIL program table
;
ILTBL    !BYTE $24, '>', $91, $27, $10, $E1, $59, $C5, $2A, $56, $10, $11, $2C
         !BYTE $8B, 'L', 'E', 'T'+$80, $A0, $80, '='+$80, $30, $BC, $E0, $13, $1D
         !BYTE $94, 'G', 'O'+$80
         !BYTE $88, 'T', 'O'+$80, $30, $BC, $E0, $10, $11, $16
         !BYTE $80, 'S', 'U', 'B'+$80, $30, $BC, $E0, $14, $16
         !BYTE $90, 'P', 'R'+$80, $83, 'I', 'N', 'T'+$80, $E5, $71, $88, ';'+$80, $E1, $1D, $8F
         !BYTE $A2, $21, $58, $6F, $83, ','+$80, $22, $55, $83, ':'+$80, $24, $93, $E0, $23, $1D
         !BYTE $30, $BC, $20, $48
         !BYTE $91, 'I', 'F'+$80, $30, $BC, $31, $34, $30, $BC
         !BYTE $84, 'T', 'H', 'E', 'N'+$80, $1C, $1D, $38, $0D
         !BYTE $9A, 'I', 'N', 'P', 'U', 'T'+$80, $A0, $10
         !BYTE $E7, $24, $3F, $20, $91, $27, $E1, $59, $81, ','+$80, $30, $BC, $13, $11
         !BYTE $82, ','+$80, $4D, $E0, $1D
         !BYTE $89, 'R', 'E', 'T', 'U', 'R', 'N'+$80, $E0, $15, $1D
         !BYTE $85, 'E', 'N', 'D'+$80, $E0, $2D
         !BYTE $98, 'L', 'I', 'S', 'T'+$80, $EC, $24, $00, $00, $00
         !BYTE $00, $0A, $80, $1F, $24, $93, $23, $1D, $30, $BC, $E1, $50, $80, ','+$80, $59
         !BYTE $85, 'R', 'U', 'N'+$80, $38, $0A
         !BYTE $86, 'C', 'L', 'E', 'A', 'R'+$80, $2B
         !BYTE $84, 'R', 'E', 'M'+$80, $1D, $A0
         !BYTE $80, '='+$80, $38, $14
         !BYTE $85, '-'+$80, $30, $D3, $17, $64
         !BYTE $81, '+'+$80, $30, $D3
         !BYTE $85, '+'+$80, $30, $D3, $18, $5A
         !BYTE $85, '-'+$80, $30, $D3, $19, $54, $2F, $30, $E2
         !BYTE $85, '*'+$80, $30, $E2, $1A, $5A
         !BYTE $85, '/'+$80, $30, $E2, $1B, $54, $2F
         !BYTE $98, 'R', 'N', 'D'+$80, $0A, $80, $80, $12, $0A, $09, $29, $1A, $0A, $1A
         !BYTE $85, $18, $13, $09, $80, $12, $01, $0B, $31, $30, $61, $72, $0B, $04, $02
         !BYTE $03, $05, $03, $1B, $1A, $19, $0B, $09, $06, $0A, $00, $00, $1C, $17, $2F
         !BYTE $8F, 'U', 'S', 'R'+$80, $80, '('+$80, $30, $BC, $31, $2A, $31, $2A, $80, ')'+$80, $2E
         !BYTE $2F, $A2, $12, $2F, $C1, $2F, $80, '('+$80, $30, $BC, $80, ')'+$80, $2F, $83, ','+$80
         !BYTE $38, $BC, $0B, $2F, $80, '('+$80, $52, $2F, $84, '='+$80, $09, $02, $2F, $8E, '<'+$80
         !BYTE $84, '='+$80, $09, $93, $2F, $84, '>'+$80, $09, $05, $2F, $09, $91, $2F, $80, '>'+$80
         !BYTE $84, '='+$80, $09, $06, $2F, $84, '<'+$80, $09, $95, $2F, $09, $04, $2F, $00, $00
         !BYTE $00

; ['24', '3E', '91',    '27', '10',   'E1', '59', 'C5', '2A', '56', '10',   '11',   '2C', '8B',    '4C', '45', 'D4', 'A0', '80',    'BD', '30', 'BC', 'E0', '13',   '1D',   '94',    '47', 'CF', '88',    '54', 'CF', '30', 'BC', 'E0', '10',   '11',   '16',   '80',    '53', '55', 'C2', '30', 'BC', 'E0', '14',   '16',   '90',    '50', 'D2', '83',    '49', '4E', 'D4', 'E5', '71', '88',    'BB', 'E1', '1D',   '8F',    'A2', '21', '58', '6F', '83',    'AC', '22', '55', '83',    'BA', '24', '93',    'E0', '23', '1D',   '30', 'BC', '20', '48', '91',    '49', 'C6', '30', 'BC', '31', '34', '30', 'BC', '84',    '54', '48', '45', 'CE', '1C',   '1D',   '38', '0D', '9A',    '49', '4E', '50', '55', 'D4', 'A0', '10',   'E7', '24', '3F', '20', '91',    '27', 'E1', '59', '81',    'AC', '30', 'BC', '13',   '11',   '82',   'AC', '4D', 'E0', '1D',   '89',  '52', '45', '54', '55', '52', 'CE', 'E0', '15',   '1D',   '85',    '45', '4E', 'C4', 'E0', '2D', '98',    '4C', '49', '53', 'D4', 'EC', '24', '00',   '00',   '00',   '00',   '0A', '80',    '1F',   '24', '93',    '23', '1D',   '30', 'BC', 'E1', '50', '80',    'AC', '59', '85',    '52', '55', 'CE', '38', '0A', '86',    '43', '4C', '45', '41', 'D2', '2B', '84',    '52', '45', 'CD', '1D',   'A0', '80',    'BD', '38', '14',   '85',    'AD', '30', 'D3', '17',   '64', '81',    'AB', '30', 'D3', '85',    'AB', '30', 'D3', '18',   '5A', '85',    'AD', '30', 'D3', '19',   '54', '2F', '30', 'E2', '85',    'AA', '30', 'E2', '1A',   '5A', '85',    'AF', '30', 'E2', '1B',   '54', '2F', '98',    '52', '4E', 'C4', '0A', '80',    '80',    '12',   '0A', '09', '29', '1A',   '0A', '1A',   '85',    '18',   '13',   '09', '80',    '12',   '01',   '0B',   '31', '30', '61', '72', '0B',   '04',   '02',   '03',   '05',   '03',   '1B',   '1A',   '19',   '0B',   '09', '06',   '0A', '00',   '00',   '1C',   '17',   '2F', '8F',    '55', '53', 'D2', '80',    'A8', '30', 'BC', '31', '2A', '31', '2A', '80',    'A9', '2E', '2F', 'A2', '12',   '2F', 'C1', '2F', '80',    'A8', '30', 'BC', '80',    'A9', '2F', '83',    'AC', '38', 'BC', '0B',   '2F', '80',    'A8', '52', '2F', '84',    'BD', '09', '02',   '2F', '8E',    'BC', '84',    'BD', '09', '93',    '2F', '84',    'BE', '09', '05',   '2F', '09', '91',    '2F', '80',    'BE', '84',    'BD', '09', '06',   '2F', '84',    'BC', '09', '95',    '2F', '09', '04',   '2F']
; ['$',  '>',  '\x11*', "'",  '\x10', 'a*', 'Y',  'E*', '*',  'V',  '\x10', '\x11', ',',  '\x0b*', 'L',  'E',  'T*', ' *', '\x00*', '=*', '0',  '<*', '`*', '\x13', '\x1d', '\x14*', 'G',  'O*', '\x08*', 'T',  'O*', '0',  '<*', '`*', '\x10', '\x11', '\x16', '\x00*', 'S',  'U', 'B*',  '0',  '<*', '`*', '\x14', '\x16', '\x10*', 'P',  'R*', '\x03*', 'I',  'N',  'T*', 'e*', 'q',  '\x08*', ';*', 'a*', '\x1d', '\x0f*', '"*', '!',  'X',  'o',  '\x03*', ',*', '"',  'U',  '\x03*', ':*', '$',  '\x13*', '`*', '#',  '\x1d', '0',  '<*', ' ',  'H',  '\x11*', 'I',  'F*', '0',  '<*', '1',  '4',  '0',  '<*', '\x04*', 'T',  'H',  'E',  'N*', '\x1c', '\x1d', '8',  '\r', '\x1a*', 'I',  'N',  'P',  'U',  'T*', ' *', '\x10', 'g*', '$',  '?',  ' ',  '\x11*', "'",  'a*', 'Y',  '\x01*', ',*', '0',  '<*', '\x13', '\x11', '\x02*', ',*', 'M', '`*', '\x1d', '\t*', 'R',  'E',  'T',  'U',  'R',  'N*', '`*', '\x15', '\x1d', '\x05*', 'E',  'N',  'D*', '`*', '-',  '\x18*', 'L',  'I',  'S',  'T*', 'l*', '$',  '\x00', '\x00', '\x00', '\x00', '\n', '\x00*', '\x1f', '$',  '\x13*', '#',  '\x1d', '0',  '<*', 'a*', 'P',  '\x00*', ',*', 'Y',  '\x05*', 'R',  'U',  'N*', '8',  '\n', '\x06*', 'C',  'L',  'E',  'A',  'R*', '+',  '\x04*', 'R',  'E',  'M*', '\x1d', ' *', '\x00*', '=*', '8',  '\x14', '\x05*', '-*', '0',  'S*', '\x17', 'd',  '\x01*', '+*', '0',  'S*', '\x05*', '+*', '0',  'S*', '\x18', 'Z',  '\x05*', '-*', '0',  'S*', '\x19', 'T',  '/',  '0',  'b*', '\x05*', '**', '0',  'b*', '\x1a', 'Z',  '\x05*', '/*', '0',  'b*', '\x1b', 'T',  '/',  '\x18*', 'R',  'N',  'D*', '\n', '\x00*', '\x00*', '\x12', '\n', '\t', ')',  '\x1a', '\n', '\x1a', '\x05*', '\x18', '\x13', '\t', '\x00*', '\x12', '\x01', '\x0b', '1',  '0',  'a',  'r',  '\x0b', '\x04', '\x02', '\x03', '\x05', '\x03', '\x1b', '\x1a', '\x19', '\x0b', '\t', '\x06', '\n', '\x00', '\x00', '\x1c', '\x17', '/',  '\x0f*', 'U',  'S',  'R*', '\x00*', '(*', '0',  '<*', '1',  '*',  '1',  '*',  '\x00*', ')*', '.',  '/',  '"*', '\x12', '/',  'A*', '/',  '\x00*', '(*', '0',  '<*', '\x00*', ')*', '/',  '\x03*', ',*', '8',  '<*', '\x0b', '/',  '\x00*', '(*', 'R',  '/',  '\x04*', '=*', '\t', '\x02', '/',  '\x0e*', '<*', '\x04*', '=*', '\t', '\x13*', '/',  '\x04*', '>*', '\t', '\x05', '/',  '\t', '\x11*', '/',  '\x00*', '>*', '\x04*', '=*', '\t', '\x06', '/',  '\x04*', '<*', '\t', '\x15*', '/',  '\t', '\x04', '/']
; http://www.nicholson.com/rhn/basic/basic.info.html#2

;
; End of Tiny Basic

;
; Begin base system initialization
;
FBLK     jsr CLRSC                  ; Go clear the screen
         ldx #$00                   ; Offset for welcome message and prompt
         jsr SNDMSG                 ; Go print it
ST_LP    jsr RCCHR                  ; Go get a character from the console
         cmp #'C'                   ; Check for 'C'
         bne IS_WRM                 ; If not branch to next check
         jmp COLD_S                 ; Otherwise cold-start Tiny Basic
IS_WRM   cmp #'W'                   ; Check for 'W'
         bne PRMPT                  ; If not, branch to re-prompt them
         jmp WARM_S                 ; Otherwise warm-start Tiny Basic
PRMPT    LDX #$22                   ; Offset of prompt in message block
         jsr SNDMSG                 ; Go print the prompt	 
         jmp ST_LP                  ; Go get the response

;
; The message block. It terminates with an FF.
;
MBLK
         !RAW   "TINY BASIC - Copyright, Tom Pitman"
         !RAW   $0D, $0D
         !RAW   "Boot (C/W)? "
         !RAW   $07, $FF

;
; Begin BIOS subroutines
;

;
; Clear the screen
;
CLRSC    jsr CLEARSCRN
         jmp HOME

;
; Print a message.
; This sub expects the message offset from MBLK in X.
;
SNDMSG   lda MBLK,X                 ; Get a character from the message block
         cmp #$FF                   ; Look for end of message marker
         beq EXSM                   ; Finish up if it is
         jsr SNDCHR                 ; Otherwise send the character
         inx                        ; Increment the pointer
         jmp SNDMSG                 ; Go get next character
EXSM     rts                        ; Return

;
; Get a character from the keyboard
; Runs into SNDCHR to provide echo
;
RCCHR    sec                        ; Wait for keypress
         jsr GETCH

;
; Send a character to the screen
;
SNDCHR   sta $FE                    ; Save the character to be printed
         cmp #$FF                   ; Check for a bunch of characters
         BEQ EXSC                   ; that we don't want to print to
         cmp #$00                   ; the terminal and discard them to
         beq EXSC                   ; clean up the output
         cmp #$91                   ;
         beq EXSC                   ;
         cmp #$93                   ;
         beq EXSC                   ;
         cmp #$80                   ;
         beq EXSC                   ;
         cmp #$0A                   ; Ignore line feed
         beq EXSC                   ;

GETSTS   jmp PRCH
EXSC     rts                        ; Return

;
; Check break routine
; Any keystroke will produce a break condition (carry set)
; Note: BREAK is renamed CHKBREAK to prevent conflict with
;       BREAK routine in SimpleMon program.
;
CHKBREAK pha
         txa
         pha
         clc                        ; set no waiting flag
         jsr GETCH                  ; if key pressed, carry is set; otherwise it is clear
         pla
         tax
         pla
         rts
