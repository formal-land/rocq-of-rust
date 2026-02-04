# Interactive Explorer

<div id="evm-explorer">
    <div class="explorer-header">
        <h2>EVM Opcode Verification Explorer</h2>
        <p>Explore the four-stage verification pipeline for each opcode</p>
    </div>

    <div class="explorer-container">
        <aside class="opcode-sidebar">
            <h3>Opcodes</h3>
            <div class="category" data-category="arithmetic">
                <h4>Arithmetic</h4>
                <ul class="opcode-list">
                    <li class="opcode-item verified" data-opcode="add">ADD</li>
                    <li class="opcode-item verified" data-opcode="mul">MUL</li>
                    <li class="opcode-item verified" data-opcode="sub">SUB</li>
                    <li class="opcode-item verified" data-opcode="div">DIV</li>
                    <li class="opcode-item verified" data-opcode="sdiv">SDIV</li>
                    <li class="opcode-item verified" data-opcode="mod">MOD</li>
                    <li class="opcode-item verified" data-opcode="smod">SMOD</li>
                    <li class="opcode-item verified" data-opcode="addmod">ADDMOD</li>
                    <li class="opcode-item verified" data-opcode="mulmod">MULMOD</li>
                    <li class="opcode-item verified" data-opcode="exp">EXP</li>
                    <li class="opcode-item verified" data-opcode="signextend">SIGNEXTEND</li>
                </ul>
            </div>
            <div class="category" data-category="bitwise">
                <h4>Comparison & Bitwise</h4>
                <ul class="opcode-list">
                    <li class="opcode-item verified" data-opcode="lt">LT</li>
                    <li class="opcode-item verified" data-opcode="gt">GT</li>
                    <li class="opcode-item verified" data-opcode="slt">SLT</li>
                    <li class="opcode-item verified" data-opcode="sgt">SGT</li>
                    <li class="opcode-item verified" data-opcode="eq">EQ</li>
                    <li class="opcode-item verified" data-opcode="iszero">ISZERO</li>
                    <li class="opcode-item verified" data-opcode="bitand">AND</li>
                    <li class="opcode-item verified" data-opcode="bitor">OR</li>
                    <li class="opcode-item verified" data-opcode="bitxor">XOR</li>
                    <li class="opcode-item verified" data-opcode="not">NOT</li>
                    <li class="opcode-item verified" data-opcode="byte">BYTE</li>
                    <li class="opcode-item verified" data-opcode="shl">SHL</li>
                    <li class="opcode-item verified" data-opcode="shr">SHR</li>
                    <li class="opcode-item verified" data-opcode="sar">SAR</li>
                </ul>
            </div>
            <div class="category" data-category="memory">
                <h4>Memory</h4>
                <ul class="opcode-list">
                    <li class="opcode-item in-progress" data-opcode="mload">MLOAD</li>
                    <li class="opcode-item in-progress" data-opcode="mstore">MSTORE</li>
                    <li class="opcode-item in-progress" data-opcode="mstore8">MSTORE8</li>
                    <li class="opcode-item in-progress" data-opcode="msize">MSIZE</li>
                </ul>
            </div>
            <div class="category" data-category="stack">
                <h4>Stack</h4>
                <ul class="opcode-list">
                    <li class="opcode-item in-progress" data-opcode="pop">POP</li>
                    <li class="opcode-item in-progress" data-opcode="push">PUSH</li>
                    <li class="opcode-item in-progress" data-opcode="dup">DUP</li>
                    <li class="opcode-item in-progress" data-opcode="swap">SWAP</li>
                </ul>
            </div>
        </aside>

        <section class="opcode-detail">
            <div class="pipeline-visualization">
                <div class="pipeline-stage" data-stage="rust">
                    <div class="stage-icon">🦀</div>
                    <div class="stage-label">Rust</div>
                    <div class="stage-status">Source</div>
                </div>
                <div class="pipeline-arrow">→</div>
                <div class="pipeline-stage" data-stage="link">
                    <div class="stage-icon">🔗</div>
                    <div class="stage-label">Link</div>
                    <div class="stage-status">Types</div>
                </div>
                <div class="pipeline-arrow">→</div>
                <div class="pipeline-stage" data-stage="simulate">
                    <div class="stage-icon">⚙️</div>
                    <div class="stage-label">Simulate</div>
                    <div class="stage-status">Model</div>
                </div>
                <div class="pipeline-arrow">→</div>
                <div class="pipeline-stage" data-stage="test">
                    <div class="stage-icon">✓</div>
                    <div class="stage-label">Test</div>
                    <div class="stage-status">Verify</div>
                </div>
            </div>

            <div class="stage-tabs">
                <button class="tab active" data-stage="rust">1. Rust Source</button>
                <button class="tab" data-stage="link">2. Link Instance</button>
                <button class="tab" data-stage="simulate">3. Simulation</button>
                <button class="tab" data-stage="test">4. Test Cases</button>
            </div>

            <div class="code-display">
                <div class="code-header">
                    <span class="opcode-name">LT</span>
                    <span class="file-path">bitwise.v</span>
                </div>
                <pre><code id="code-content" class="language-rocq">Select an opcode from the sidebar to view its verification code.</code></pre>
            </div>

            <div class="explanation">
                <h4>About this stage</h4>
                <p id="stage-explanation">
                    The verification pipeline has four stages. Click on an opcode and tab to explore each stage of the formal verification process.
                </p>
            </div>
        </section>
    </div>
</div>

<script>
// Explorer initialization is handled by explorer.js
document.addEventListener('DOMContentLoaded', function() {
    if (typeof EVMExplorer !== 'undefined') {
        EVMExplorer.init();
    }
});
</script>
