// See LICENSE.SiFive for license details.
// See LICENSE.Berkeley for license details.

package freechips.rocketchip.rocket

import chisel3._
import chisel3.util.{BitPat, Fill, Cat, Reverse, PriorityEncoderOH, PopCount, MuxLookup}
import org.chipsalliance.cde.config.Parameters
import freechips.rocketchip.tile.CoreModule
import freechips.rocketchip.util._

object ALU {
  val SZ_ALU_FN = 5
  def FN_X    = BitPat("b?????")
  def FN_ADD  = 0.U
  def FN_SL   = 1.U
  def FN_SEQ  = 2.U
  def FN_SNE  = 3.U
  def FN_XOR  = 4.U
  def FN_SR   = 5.U
  def FN_OR   = 6.U
  def FN_AND  = 7.U
  def FN_CZEQZ = 8.U
  def FN_CZNEZ = 9.U
  def FN_SUB  = 10.U
  def FN_SRA  = 11.U
  def FN_SLT  = 12.U
  def FN_SGE  = 13.U
  def FN_SLTU = 14.U
  def FN_SGEU = 15.U
  def FN_UNARY = 16.U
  def FN_ROL  = 17.U
  def FN_ROR  = 18.U
  def FN_BEXT = 19.U

  // MBP -- the packed-SIMD four, ALU-integrated, custom-0.  See
  // fpga/pynq-z2/docs/PEXT_SPEC.md and the bit-exact C reference in
  // fpga/pynq-z2/sw/pext.h.  20-23 and 27 are the only free codes in this 5-bit
  // space (0-19, 24-26 and 28-31 are taken); four ops take four of them, and 27
  // is left for a fifth.
  def FN_PDOT8  = 20.U
  def FN_PMAX8  = 21.U
  def FN_PQMUL  = 22.U
  def FN_PCLIP8 = 23.U
  def FN_PEXT   = BitPat("b101??")   // 20..23, i.e. exactly the four above

  def FN_ANDN = 24.U
  def FN_ORN  = 25.U
  def FN_XNOR = 26.U

  def FN_MAX  = 28.U
  def FN_MIN  = 29.U
  def FN_MAXU = 30.U
  def FN_MINU = 31.U
  def FN_MAXMIN = BitPat("b111??")

  // Mul/div reuse some integer FNs
  def FN_DIV  = FN_XOR
  def FN_DIVU = FN_SR
  def FN_REM  = FN_OR
  def FN_REMU = FN_AND

  def FN_MUL    = FN_ADD
  def FN_MULH   = FN_SL
  def FN_MULHSU = FN_SEQ
  def FN_MULHU  = FN_SNE

  def isMulFN(fn: UInt, cmp: UInt) = fn(1,0) === cmp(1,0)
  def isSub(cmd: UInt) = cmd(3)
  def isCmp(cmd: UInt) = (cmd >= FN_SLT && cmd <= FN_SGEU)
  def isMaxMin(cmd: UInt) = (cmd >= FN_MAX && cmd <= FN_MINU)
  def cmpUnsigned(cmd: UInt) = cmd(1)
  def cmpInverted(cmd: UInt) = cmd(0)
  def cmpEq(cmd: UInt) = !cmd(3)
  def shiftReverse(cmd: UInt) = !cmd.isOneOf(FN_SR, FN_SRA, FN_ROR, FN_BEXT)
  def bwInvRs2(cmd: UInt) = cmd.isOneOf(FN_ANDN, FN_ORN, FN_XNOR)
}

import ALU._


abstract class AbstractALU(implicit p: Parameters) extends CoreModule()(p) {
  val io = IO(new Bundle {
    val dw = Input(UInt(SZ_DW.W))
    val fn = Input(UInt(SZ_ALU_FN.W))
    val in2 = Input(UInt(xLen.W))
    val in1 = Input(UInt(xLen.W))
    val out = Output(UInt(xLen.W))
    val adder_out = Output(UInt(xLen.W))
    val cmp_out = Output(Bool())
  })
}

class ALU(implicit p: Parameters) extends AbstractALU()(p) {
  override def desiredName = "RocketALU"

  // ADD, SUB
  val in2_inv = Mux(isSub(io.fn), ~io.in2, io.in2)
  val in1_xor_in2 = io.in1 ^ in2_inv
  val in1_and_in2 = io.in1 & in2_inv
  io.adder_out := io.in1 + in2_inv + isSub(io.fn)

  // SLT, SLTU
  val slt =
    Mux(io.in1(xLen-1) === io.in2(xLen-1), io.adder_out(xLen-1),
    Mux(cmpUnsigned(io.fn), io.in2(xLen-1), io.in1(xLen-1)))
  io.cmp_out := cmpInverted(io.fn) ^ Mux(cmpEq(io.fn), in1_xor_in2 === 0.U, slt)

  // SLL, SRL, SRA
  val (shamt, shin_r) =
    if (xLen == 32) (io.in2(4,0), io.in1)
    else {
      require(xLen == 64)
      val shin_hi_32 = Fill(32, isSub(io.fn) && io.in1(31))
      val shin_hi = Mux(io.dw === DW_64, io.in1(63,32), shin_hi_32)
      val shamt = Cat(io.in2(5) & (io.dw === DW_64), io.in2(4,0))
      (shamt, Cat(shin_hi, io.in1(31,0)))
    }
  val shin = Mux(shiftReverse(io.fn), Reverse(shin_r), shin_r)
  val shout_r = (Cat(isSub(io.fn) & shin(xLen-1), shin).asSInt >> shamt)(xLen-1,0)
  val shout_l = Reverse(shout_r)
  val shout = Mux(io.fn === FN_SR || io.fn === FN_SRA || io.fn === FN_BEXT, shout_r, 0.U) |
              Mux(io.fn === FN_SL,                                          shout_l, 0.U)

  // CZEQZ, CZNEZ
  val in2_not_zero = io.in2.orR
  val cond_out = Option.when(usingConditionalZero)(
    Mux((io.fn === FN_CZEQZ && in2_not_zero) || (io.fn === FN_CZNEZ && !in2_not_zero), io.in1, 0.U)
  )

  // AND, OR, XOR
  val logic = Mux(io.fn === FN_XOR || io.fn === FN_OR || io.fn === FN_ORN || io.fn === FN_XNOR, in1_xor_in2, 0.U) |
              Mux(io.fn === FN_OR || io.fn === FN_AND || io.fn === FN_ORN || io.fn === FN_ANDN, in1_and_in2, 0.U)

  val bext_mask = Mux(coreParams.useZbs.B && io.fn === FN_BEXT, 1.U, ~(0.U(xLen.W)))
  val shift_logic = (isCmp (io.fn) && slt) | logic | (shout & bext_mask)
  val shift_logic_cond = cond_out match {
    case Some(co) => shift_logic | co
    case _ => shift_logic
  }

  // CLZ, CTZ, CPOP
  val tz_in = MuxLookup((io.dw === DW_32) ## !io.in2(0), 0.U)(Seq(
    0.U -> io.in1,
    1.U -> Reverse(io.in1),
    2.U -> 1.U ## io.in1(31,0),
    3.U -> 1.U ## Reverse(io.in1(31,0))
  ))
  val popc_in = Mux(io.in2(1),
    Mux(io.dw === DW_32, io.in1(31,0), io.in1),
    PriorityEncoderOH(1.U ## tz_in) - 1.U)(xLen-1,0)
  val count = PopCount(popc_in)
  val in1_bytes = io.in1.asTypeOf(Vec(xLen / 8, UInt(8.W)))
  val orcb = VecInit(in1_bytes.map(b => Fill(8, b =/= 0.U))).asUInt
  val rev8 = VecInit(in1_bytes.reverse).asUInt
  val unary = MuxLookup(io.in2(11,0), count)(Seq(
    0x287.U -> orcb,
    (if (xLen == 32) 0x698 else 0x6b8).U -> rev8,
    0x080.U -> io.in1(15,0),
    0x604.U -> Fill(xLen-8, io.in1(7)) ## io.in1(7,0),
    0x605.U -> Fill(xLen-16, io.in1(15)) ## io.in1(15,0)
  ))

  // MAX, MIN, MAXU, MINU
  val maxmin_out = Mux(io.cmp_out, io.in2, io.in1)

  // ROL, ROR
  val rot_shamt = Mux(io.dw === DW_32, 32.U, xLen.U) - shamt
  val rotin = Mux(io.fn(0), shin_r, Reverse(shin_r))
  val rotout_r = (rotin >> rot_shamt)(xLen-1,0)
  val rotout_l = Reverse(rotout_r)
  val rotout = Mux(io.fn(0), rotout_r, rotout_l) | Mux(io.fn(0), shout_l, shout_r)

  // MBP packed SIMD -- DOT8, MAX8, QMUL, CLIP8.  Elaborated only when
  // coreParams.usePExt, so a hart without it gets an ALU that is bit-identical to
  // the stock one (that is the property the patch's before/after Verilog diff checks).
  //
  // THE SPECIFICATION IS fpga/pynq-z2/sw/pext.h's mb_pext_*_sw.  If this and that
  // disagree, this is wrong.  Adapted from the measured out-of-context datapaths in
  // fpga/pynq-z2/rtl_study/pext/: pext_pdot8_lut.v (depth-3, ACC=0, signed only),
  // pext_pmaxmin8.v (max, signed), and the pmulscale/clamp halves of
  // pext_prequant.v -- NOT its fused requant2, whose 48-bit rounding barrel shifter
  // is what missed timing (PEXT_FEASIBILITY.md 1.4).
  val pext_ops: Seq[(UInt, UInt)] = if (!coreParams.usePExt) Nil else {
    require(xLen == 64, "MBP packed SIMD is defined on RV64 only (8 int8 lanes per register)")
    val a8 = io.in1.asTypeOf(Vec(8, SInt(8.W)))
    val b8 = io.in2.asTypeOf(Vec(8, SInt(8.W)))

    // MBP.DOT8: eight signed 8x8 products summed by a depth-3 balanced adder tree.
    // |result| <= 8*128*128 = 131072, so 19 bits signed is exact; the 64-bit
    // destination can never overflow and there is no saturation to get wrong.
    val prod = (a8 zip b8).map { case (x, y) => x * y }        // SInt(16.W) each
    val dot1 = Seq.tabulate(4)(i => prod(2*i) +& prod(2*i+1))  // 17 bits
    val dot2 = Seq.tabulate(2)(i => dot1(2*i) +& dot1(2*i+1))  // 18 bits
    val dot  = dot2(0) +& dot2(1)                              // 19 bits
    val dot8 = Cat(Fill(xLen - 19, dot(18)), dot.asUInt)

    // MBP.MAX8: eight independent signed byte maxima.  ReLU is this against x0.
    val max8 = VecInit((a8 zip b8).map { case (x, y) => Mux(x > y, x, y) }).asUInt

    // MBP.QMUL: (sext32(rs1) * sext32(rs2) + 2^30) >>> 31.
    // ROUND-HALF-UP: add the rounding constant, then an ARITHMETIC shift.  Not
    // half-away-from-zero and not half-to-even -- that difference is 1 LSB on
    // roughly half of all negative outputs.  The product and the sum are exact
    // (64 and 65 bits), so this is the C expression with no approximation in it.
    val qprod = io.in1(31,0).asSInt * io.in2(31,0).asSInt      // SInt(64.W), exact
    val qsum  = qprod +& (BigInt(1) << 30).S                   // SInt(65.W), exact
    val qhi   = qsum >> 31                                     // SInt(34.W), arithmetic
    val qmul  = Cat(Fill(xLen - 34, qhi(33)), qhi.asUInt)

    // MBP.CLIP8: sext64(clamp(rs1, -128, +127)); rs2 ignored.  Two levels: the
    // clamp is decided by the bits above the byte, not by a comparator chain.
    val cq  = io.in1
    val chi = ~cq(xLen-1) &  cq(xLen-2,7).orR    // > +127
    val clo =  cq(xLen-1) & ~cq(xLen-2,7).andR   // < -128
    val cb  = Mux(chi, 0x7f.U(8.W), Mux(clo, 0x80.U(8.W), cq(7,0)))
    val clip8 = Cat(Fill(xLen - 8, cb(7)), cb)

    Seq(FN_PDOT8 -> dot8, FN_PMAX8 -> max8, FN_PQMUL -> qmul, FN_PCLIP8 -> clip8)
  }

  val out = MuxLookup(io.fn, shift_logic_cond)(Seq(
    FN_ADD -> io.adder_out,
    FN_SUB -> io.adder_out
  ) ++ pext_ops ++ (if (coreParams.useZbb) Seq(
    FN_UNARY -> unary,
    FN_MAX -> maxmin_out,
    FN_MIN -> maxmin_out,
    FN_MAXU -> maxmin_out,
    FN_MINU -> maxmin_out,
    FN_ROL -> rotout,
    FN_ROR -> rotout,
  ) else Nil))


  io.out := out
  if (xLen > 32) {
    require(xLen == 64)
    when (io.dw === DW_32) { io.out := Cat(Fill(32, out(31)), out(31,0)) }
  }
}
