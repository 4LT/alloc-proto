(() => {
    class Handle {
        constructor(id, idx) {
            this.id = id;
            this.idx = idx;
            Handle.newId++;
        }

        id;
        idx;
    }

    class BlockStart {
        constructor(blockCt) {
            this.blockCt = blockCt;
        }

        id = 0;
        blockCt;
    }

    class OccupiedStart extends BlockStart {
        constructor(blockCt, id) {
            super(blockCt);
            this.id = id;
        }

        value = "";
    }

    class FreeStart extends BlockStart {
        constructor(blockCt) {
            super(blockCt);
        }

        prev = 0;
        next = 0;
    }

    const NULL_BLOCK = Symbol();
    const FREE_REST_BLOCK = Symbol();
    const OCCUPIED_REST_BLOCK = Symbol();

    const EMOJI = Object.freeze({
        CHECK: '\u2705',
        RED_X: '\u274c',
    });

    class Allocator {
        constructor(maxSegmentSz) {
            this.maxOrder = ceil_log2(maxSegmentSz);
            this.maxAlign = 2 ** this.maxOrder;
            this.reset();
        }

        memory;
        freeHeads;
        nextId;
        maxOrder;
        maxAlign;

        reset() {
            this.memory = [NULL_BLOCK];
            this.freeHeads = new Array(ceil_log2(this.maxOrder + 1)).fill(0);
            this.nextId = 1;
        }

        alloc(blockCt) {
            const block = new OccupiedStart(blockCt, this.nextId);
            this.nextId++;
            let blockOrder = ceil_log2(blockCt);
            let blockAlign = 2 ** blockOrder;
            let idx;

            let order = blockOrder;
            let align = blockAlign;
            while (order <= this.maxOrder) {
                if (this.freeHeads[order] > 0) {
                    let blocksLeft = blockCt;
                    const gap = align - blockCt;
                    idx = this._popFree(order);
                    this.memory[idx] = block;

                    blocksLeft--;
                    let ofs = 1;

                    for (; blocksLeft > 0; blocksLeft--, ofs++) {
                        this.memory[idx + ofs] = OCCUPIED_REST_BLOCK;
                    }

                    this._fillFree(idx + ofs, gap);
                    break;
                }

                order++;
                align*= 2;
            }

            if (order > this.maxOrder) {
                let blocksLeft = blockCt;
                const gap = (
                    blockAlign - this.memory.length % blockAlign
                ) % blockAlign;

                idx = this.memory.length + gap;
                this._fillFree(this.memory.length, gap);
                this.memory.push(block);
                blocksLeft--;

                for (; blocksLeft > 0; blocksLeft--) {
                    this.memory.push(OCCUPIED_REST_BLOCK);
                }
            }

            return new Handle(block.id, idx);
        }

        free(handle) {
            const blockStart = this.get(handle);

            if (blockStart == null) {
                return false;
            }

            let idx = handle.idx;
            let blockOrder = ceil_log2(blockStart.blockCt);
            let blockAlign = 2 ** blockOrder;
            let freeCt = blockStart.blockCt;

            while (blockAlign < this.maxAlign) {
                const leftIdx =
                    Math.floor(idx / blockAlign / 2) * blockAlign * 2;

                if (leftIdx === 0) {
                    break;
                }

                if (leftIdx !== idx) {
                    const leftBlock = this.memory[leftIdx];

                    if (
                        leftBlock.id === 0
                        && leftBlock.blockCt === blockAlign
                    ) {
                        freeCt+= blockAlign;
                        idx = leftIdx;
                        this._removeFree(leftIdx, blockOrder);
                    } else {
                        break;
                    }
                } 

                blockOrder++;
                blockAlign*= 2;
            }

            let rightOfs = 0;
            while (rightOfs <= this.maxAlign / 2) {
                const rightIdx = idx + freeCt + rightOfs;

                if (rightIdx >= this.memory.length) {
                    break;
                }

                const rightBlock = this.memory[rightIdx];
                const rightOrder = ceil_log2(rightBlock.blockCt);

                if (rightBlock.id === 0) {
                    rightOfs+= rightBlock.blockCt;
                    this._removeFree(rightIdx, rightOrder);
                } else {
                    break;
                }
            }
            freeCt+= rightOfs;

            if (idx + freeCt === this.memory.length) {
                this.memory = this.memory.slice(0, idx);
            } else {
                this._fillFree(idx, freeCt);
            }

            return true;
        }

        get(handle) {
            if (handle.id === 0) {
                console.warn("get: bad handle, id cannot be 0");
                return null;
            }

            if (handle.idx <= 0 || handle.idx >= this.memory.length) {
                console.warn("get: handle out of bounds");
                return null;
            }

            for (let align = this.maxAlign; align > 1; align/= 2) {
                const probeIdx = Math.floor(handle.idx / align) * align;

                if (probeIdx === 0 || probeIdx === handle.idx) {
                    continue;
                }

                const probeBlock = this.memory[probeIdx];

                if (
                    probeBlock.blockCt + probeIdx > handle.idx
                ) {
                    console.warn("get: handle inside segment body");
                    return null;
                }
            }
            
            const block = this.memory[handle.idx];

            if (block.id === handle.id) {
                return block;
            } else {
                if (block.id === 0) {
                    console.warn("get: handle idx points to free segment");
                } else {
                    console.warn("get: handle is invalid for segment");
                }

                return null;
            }
        }

        *allocations() {
            let idx = 1;
            while (idx < this.memory.length) {
                const segment = this.memory[idx];

                if (segment.id > 0) {
                    yield [idx, segment];
                }

                idx+= segment.blockCt;
            }
        }

        _fillFree(idx, blockCt) {
            while (blockCt > 0) {
                const idxMaxOrder = this._maxOrderForIdx(idx);
                const blockMaxOrder = floor_log2(blockCt);
                const order = Math.min(blockMaxOrder, idxMaxOrder);
                const align = 2 ** order;
                const freeStart = new FreeStart(align);
                
                this.memory[idx] = freeStart;

                for (let ofs = 1; ofs < align; ofs++) {
                    this.memory[idx + ofs] = FREE_REST_BLOCK;
                }

                this._pushFree(idx, order);

                idx+= align;
                blockCt-= align;
            }
        }

        _pushFree(idx, order) {
            const node = this.memory[idx];

            if (!(node instanceof FreeStart)) {
                throw new Error("_pushFree: Wrong block type");
            }

            node.next = this.freeHeads[order];
            node.prev = 0;

            if (node.next > 0) {
                this.memory[node.next].prev = idx;
            }

            this.freeHeads[order] = idx;
        }

        _popFree(order) {
            const idx = this.freeHeads[order];
            const node = this.memory[idx];

            if (!(node instanceof FreeStart)) {
                throw new Error("_popFree: Wrong block type");
            }

            this.freeHeads[order] = node.next;

            if (node.next > 0) {
                this.memory[node.next].prev = 0;
            }

            return idx;
        }

        _removeFree(idx, order) {
            const node = this.memory[idx];

            if (!(node instanceof FreeStart)) {
                throw new Error("_removeFree: Wrong block type");
            }

            if (node.prev > 0) {
                this.memory[node.prev].next = node.next;
                
                if (node.next > 0) {
                    this.memory[node.next].prev = node.prev;
                }
            } else {
                if (this.freeHeads[order] !== idx) {
                    throw new Error("_removeFree: Orphaned free node");
                }

                this._popFree(order);
            }
        }

        _maxOrderForIdx(idx) {
            let align = this.maxAlign;
            let order = this.maxOrder;

            while (idx % align > 0) {
                align/= 2;
                order--;
            }

            return order;
        }
    }

    class Application {
        constructor(maxSegmentSz) {
            this.reset = function() {
                this.allocator = new Allocator(maxSegmentSz);
                this.handles = [];
            }

            this.reset();
        }

        allocator;
        handles;
        reset;

        free(handle) {
            return this.allocator.free(handle);
        }

        alloc(blockCt) {
            const handle = this.allocator.alloc(blockCt);
            this.handles.push(handle);
            return handle;
        }

        getEntity(handle) {
            return this.allocator.get(handle);
        }

        allocations() {
            return this.allocator.allocations();
        }

        render(ctx) {
            const {
                allocContainer,
            } = ctx;
            
            this._renderMemory(allocContainer);
            this._renderHandles(ctx);
        }

        _renderMemory(allocContainer) {
            const children = [...allocContainer.children];

            for (const child of children) {
                child.remove();
            }

            for (const block of this.allocator.memory) {
                const blockEl = document.createElement('DIV');
                const classes = ["block"];

                if (testFree(block)) {
                    classes.push("free");
                } else if (testOccupied(block)) {
                    classes.push("occupied");
                } else if (block === NULL_BLOCK) {
                    classes.push("null");
                } else {
                    classes.push("unused");
                }

                if (testStart(block)) {
                    blockEl.innerText = "start";
                    classes.push("block-start");
                }

                blockEl.classList = classes.join(" ");
                allocContainer.appendChild(blockEl);
            }
        }

        _renderHandles(ctx) {
            const {
                allocContainer,
                handleContainer,
            } = ctx;

            const children = [...handleContainer.children];

            for (const child of children) {
                child.remove();
            }

            this.handles.forEach((handle, handleIdx) => {
                const handleEl = document.createElement('TR');
                const idEl = document.createElement('TD');
                const idxEl = document.createElement('TD');
                const controlsEl = document.createElement('TD');
                const responseEl = document.createElement('TD');
                const freeBtn = document.createElement('BUTTON');
                const removeBtn = document.createElement('BUTTON');
                const readBtn = document.createElement('BUTTON');
                const writeBtn = document.createElement('BUTTON');
                const readWriteField = document.createElement('INPUT');

                const signalResponse = (text) => {
                    const element = document.createElement('SPAN');
                    element.innerText = text;
                    responseEl.appendChild(element);

                    window.setTimeout(() => {
                        element.remove();
                    }, 500);
                };

                idEl.innerText = String(handle.id);
                idxEl.innerText = String(handle.idx);

                idEl.classList = "numeric";
                idxEl.classList = "numeric";
                responseEl.classList = "response";
                controlsEl.classList = "controls-cell";

                freeBtn.type = "button";
                freeBtn.innerText = "Free";

                freeBtn.addEventListener('click', () => {
                    const success = this.free(handle);

                    if (success) {
                        signalResponse(EMOJI.CHECK);
                        this._renderMemory(allocContainer);
                    } else {
                        signalResponse(EMOJI.RED_X);
                    }
                });

                removeBtn.type = "button";
                removeBtn.innerText = "Remove Handle";

                removeBtn.addEventListener('click', () => {
                    this.handles.splice(handleIdx, 1);
                    this._renderHandles(ctx);
                });

                readBtn.type = "button";
                readBtn.innerText = "Read";

                readBtn.addEventListener('click', () => {
                    const ent = this.getEntity(handle);

                    if (ent) {
                        readWriteField.value = ent.value;
                        readWriteField.classList.remove("no-value");
                        signalResponse(EMOJI.CHECK);
                    } else {
                        readWriteField.value = "Nothing";
                        readWriteField.classList.add("no-value");
                        signalResponse(EMOJI.RED_X);
                    }
                });

                writeBtn.addEventListener('click', () => {
                    if (readWriteField.classList.contains("no-value")) {
                        signalResponse(EMOJI.RED_X);
                    } else {
                        const ent =  this.getEntity(handle);

                        if (ent) {
                            ent.value = readWriteField.value;
                            signalResponse(EMOJI.CHECK);
                        } else {
                            signalResponse(EMOJI.RED_X);
                        }
                    }
                });

                writeBtn.type = "button";
                writeBtn.innerText = "Write";

                readWriteField.type = "text";

                readWriteField.addEventListener('focus', () => {
                    if (readWriteField.classList.contains("no-value")) {
                        readWriteField.classList.remove("no-value");
                        readWriteField.value = "";
                    }
                });

                controlsEl.appendChild(freeBtn);
                controlsEl.appendChild(removeBtn);
                controlsEl.appendChild(readBtn);
                controlsEl.appendChild(writeBtn);
                controlsEl.appendChild(readWriteField);
                handleEl.appendChild(idEl);
                handleEl.appendChild(idxEl);
                handleEl.appendChild(controlsEl);
                handleEl.appendChild(responseEl);
                handleContainer.appendChild(handleEl);
            });
        }
    }

    const testFree = (block) => {
        return block === FREE_REST_BLOCK || block instanceof FreeStart;
    }

    const testOccupied = (block) => {
        return block === OCCUPIED_REST_BLOCK || block instanceof OccupiedStart;
    }

    const testStart = (block) => {
        return block instanceof FreeStart || block instanceof OccupiedStart;
    }

    const ceil_log2 = (x) => {
        let l = 0;

        while (x > 1) {
            x /= 2;
            l++;
        }

        return l;
    }

    const floor_log2 = (x) => {
        let l = -1;

        while (x >= 1) {
            x /= 2;
            l++;
        }

        return l;
    }

    window.addEventListener('load', () => {
        const allocBtn = document.getElementById("alloc-button");
        const resetBtn = document.getElementById("reset-button");
        const allocInput = document.getElementById("alloc-input");
        const allocContainer = document.getElementById("allocation");
        const handleContainer = document.getElementById("handles");
        const app = new Application(Number(allocInput.max));

        const context = {
            allocContainer,
            handleContainer,
        };

        app.render(context);

        allocBtn.addEventListener('click', () => {
            const blockCt = Number(allocInput.value);
            app.alloc(blockCt);
            app.render(context);
        });

        resetBtn.addEventListener('click', () => {
            app.reset();
            app.render(context);
        });
    });
})();
