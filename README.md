# 🧪 Advance Hardware Verification Labs

### 🔧 University of Applied Sciences Bremen  
**Course:** Hardware Verification with SystemVerilog  
**Instructor:** Prof. Dr.-Ing. Stefan Wolter

---

## Lab 1: Verification of a Synchronous FIFO

### 📌 Objective:
To verify a synchronous FIFO design using SystemVerilog testbench and the OVL FIFO checker.

### 🔍 DUT Summary:
- VHDL-based FIFO.
- Parameters: `B` (bits per word), `W` (address width, 2^W words).
- Ports: `clk`, `rst`, `write`, `read`, `din[B-1:0]`, `dout[B-1:0]`, `full`, `empty`.

### ✅ Functional Features:
- Push on rising edge of `clk` if `write` is high and FIFO not full.
- Pop on rising edge of `clk` if `read` is high and FIFO not empty.
- Reset (`rst`) clears the buffer and initializes flags.
- Handles invalid read/write gracefully without corrupting state.

### 📁 File Structure:


### ⚙️ Tasks:
1. Instantiate:
   - DUT (`sync_fifo`)
   - Program module (`fifo_prog`)
   - OVL checker (`ovl_fifo`)
2. Complete the testbench (`fifo_tb.sv`)
3. Compile and simulate using `run_lab_1.do`
4. Observe:
   - Assertion results
   - Coverage data (code, functional, assertion)
5. Configure OVL checker with:
   - Proper parameters (`pass_thru`, `value_check`, etc.)
   - Coverage level `OVL_COVER_ALL`

---

## Lab 2: Verification of a 4-Bit Gray Counter

### 📌 Objective:
To verify a 4-bit gray-code counter using simulation and assertions in SystemVerilog.

### 🔍 DUT Summary:
- VHDL-based 4-bit Gray counter.
- Ports: `clk`, `rst_n` (async, active low), `en`, `dout[3:0]`.

### ✅ Functional Features:
- Asynchronous reset (`rst_n`) sets `dout` to 0000.
- Counter advances on rising `clk` if `en = 1`.
- Outputs 16-step Gray code sequence.

### 📁 File Structure:


### ⚙️ Tasks:
1. Load and simulate using `run_lab_2.do`.
2. Modify testbench to achieve 100% code coverage.
3. Implement 3 assertions:
   - `a_reset`: Immediate assertion to check reset.
   - `a_enable`: Check enable-controlled counting.
   - `a_gray_check`: Verify Gray-coded transitions.
4. Use ATV tool to debug and verify assertion behavior.

---

## 🛠 Tools & Notes

- Simulation tool: **Questa** (with GUI, assertions, and coverage analysis).
- Coverage types: Statement, Condition, Branch, FSM.
- Testbench and assertions use SystemVerilog.
- OVL (Open Verification Library) used in Lab 1 for FIFO checking.
