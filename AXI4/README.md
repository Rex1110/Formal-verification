# AXI4 Protocol Checkers 


Formal verification tool: **Cadence jasper**

基於 [AMBA® AXI™ and ACE™ Protocol Specification](<http://www.gstitt.ece.ufl.edu/courses/fall15/eel4720_5721/labs/refs/AXI4_specification.pdf>) 
和 [AXI Protocol Checker LogiCORE IP Product Guide](<https://docs.amd.com/r/en-US/pg101-axi-protocol-checker/Introduction>) 所撰寫 property。

AXI4 bus 設計在此 [repository](<https://github.com/Rex1110/rv32i-axi4-platform>)。

![checker](https://github.com/Rex1110/Formal-verification/assets/123956376/9f59b110-a11c-4caa-a612-c61d6269c5fa)



## **1. Symbolic representation**
- ✅: 斷言通過。

- ❌: 斷言失敗。

- ❗: 斷言先驗條件未成立。

## **2. Write address channel cheacks**

### ❌ AXI_ERRM_AWADDR_BOUNDARY
#### - **Description:** A write burst cannot cross a 4 KB boundary.

![1](https://github.com/Rex1110/Formal-verification/assets/123956376/e92fb93e-f80d-46c1-b502-10af3c26755c)


![AXI_ERRM_AWADDR_BOUNDARY_wave](https://github.com/Rex1110/Formal-verification/assets/123956376/588622fb-9b40-4fbb-b188-0520ea61d9e9)


AWADDR = 32'hffff_fffd \
AWLEN = 4'd0000 \
AWSIZE = 3'b010 

End of address = 32'hffff_fffd + 1 * 4bytes = 32'h0000_0001

根據此條斷言可使用位置必須落在 4 KB 區間而，32'hffff_fffd 跨至 32'h0000_0001，因此斷言失敗。

### ✅ AXI_ERRM_AWBURST
#### - **Description:** A value of 2’b11 on AWBURST is not permitted when AWVALID is High.

![2](https://github.com/Rex1110/Formal-verification/assets/123956376/8451cbd2-7c59-4693-817a-fb07bad91784)


### ✅ AXI_ERRM_AWSIZE
#### - **Description:** The size of a write transfer does not exceed the width of the data interface.

![3](https://github.com/Rex1110/Formal-verification/assets/123956376/df074afc-bfe5-4b0f-ae10-dfe8b145d44e)


### ✅ AXI_ERRM_AWVALID_RESET
#### - **Description:** AWVALID is Low for the first cycle after ARESETn goes High.

![4](https://github.com/Rex1110/Formal-verification/assets/123956376/f44b8ce3-ddb5-4432-af49-73b7f7e3f811)


### ✅ AXI_ERRM_AWADDR_STABLE
#### - **Description:** Handshake Checks: AWADDR must remain stable when AWVALID is asserted and AWREADY Low.

![5](https://github.com/Rex1110/Formal-verification/assets/123956376/01f7232d-73e3-4692-a421-0071e9b28368)


### ✅ AXI_ERRM_AWBURST_STABLE
#### - **Description:** Handshake Checks: AWBURST must remain stable when AWVALID is asserted and AWREADY Low.

![6](https://github.com/Rex1110/Formal-verification/assets/123956376/9669e109-55c9-48d9-9a9e-edf6789a3ac3)


### ✅ AXI_ERRM_AWID_STABLE
#### - **Description:** Handshake Checks: AWID must remain stable when AWVALID is asserted and AWREADY Low.

![7](https://github.com/Rex1110/Formal-verification/assets/123956376/58b52035-ef74-4c61-b87d-c71574490e18)


### ✅ AXI_ERRM_AWLEN_STABLE
#### - **Description:** Handshake Checks: AWLEN must remain stable when AWVALID is asserted and AWREADY Low.

![8](https://github.com/Rex1110/Formal-verification/assets/123956376/e0cdec7b-04f4-40a7-9429-968931af78b9)


### ✅ AXI_ERRM_AWSIZE_STABLE
#### - **Description:** Handshake Checks: AWSIZE must remain stable when AWVALID is asserted and AWREADY Low.

![9](https://github.com/Rex1110/Formal-verification/assets/123956376/fada3566-1600-4333-b733-4d6b55efa359)


### ✅ AXI_ERRM_AWVALID_STABLE
#### - **Description:** Handshake Checks: Once AWVALID is asserted, it must remain asserted until AWREADY is High.

![10](https://github.com/Rex1110/Formal-verification/assets/123956376/bac47d11-c50f-4369-b81f-11c22aa1ed1a)


## **3. Write address channel cheacks**

### ✅ AXI_ERRM_WDATA_NUM
#### - **Description:** The number of write data items matches AWLEN for the corresponding address. This is triggered when any of the following occurs:

- Write data arrives, WLAST is set, and the WDATA count is not equal to AWLEN.
- Write data arrives, WLAST is not set, and the WDATA count is equal to AWLEN.
- ADDR arrives, WLAST is already received, and the WDATA count is not equal to AWLEN.


![11](https://github.com/Rex1110/Formal-verification/assets/123956376/a4e4dd84-a47b-4ead-9973-6e2df5934a80)


### ❗ AXI_ERRM_WSTRB
#### - **Description:** Write strobes must only be asserted for the correct byte lanes as determined from the: Start Address, Transfer Size and Beat Number.

![12](https://github.com/Rex1110/Formal-verification/assets/123956376/97bda00f-05e5-43a4-bc18-4e189622af77)


### ✅ AXI_ERRM_WVALID_RESET
#### - **Description:** WVALID is LOW for the first cycle after ARESETn goes High.

![13](https://github.com/Rex1110/Formal-verification/assets/123956376/e9fcc715-cbab-4c65-b7e8-134c90b7bf86)


### ❗ AXI_ERRM_WDATA_STABLE
#### - **Description:** Handshake Checks: WDATA must remain stable when WVALID is asserted and WREADY Low.

![14](https://github.com/Rex1110/Formal-verification/assets/123956376/a7fb681b-5922-4561-ac4a-56cf72375b8f)


### ❗ AXI_ERRM_WLAST_STABLE
#### - **Description:** Handshake Checks: WLAST must remain stable when WVALID is asserted and WREADY Low.

![15](https://github.com/Rex1110/Formal-verification/assets/123956376/43477f46-5c97-4245-bbf8-04515ff22384)


### ❗ AXI_ERRM_WSTRB_STABLE
#### - **Description:** Handshake Checks: WSTRB must remain stable when WVALID is asserted and WREADY Low.

![16](https://github.com/Rex1110/Formal-verification/assets/123956376/3e634011-f4bb-46a5-ab37-96a8e68d6c4e)


### ❗ AXI_ERRM_WVALID_STABLE
#### - **Description:** Handshake Checks: Once WVALID is asserted, it must remain asserted until WREADY is High.

![17](https://github.com/Rex1110/Formal-verification/assets/123956376/447075a4-31fc-46f0-9b8f-f8b24e69f1a5)


## **4. Write response channel cheacks**

### ✅ AXI_ERRS_BVALID_RESET
#### - **Description:** BVALID is Low for the first cycle after ARESETn goes High.

![18](https://github.com/Rex1110/Formal-verification/assets/123956376/0d5ed0d1-b95e-4d7d-b6a2-1fda51193e08)


### ✅ AXI_ERRS_BRESP_WLAST
#### - **Description:** A slave must not take BVALID HIGH until after the last write data handshake is complete.

![19](https://github.com/Rex1110/Formal-verification/assets/123956376/6aff66fa-2be8-420f-a17d-a217f635e2e1)


### ❗ AXI_ERRS_BID_STABLE
#### - **Description:** Handshake Checks: BID must remain stable when BVALID is asserted and BREADY Low.

![20](https://github.com/Rex1110/Formal-verification/assets/123956376/7df5f129-a6eb-4cf7-932f-7c1f06e7ab11)


### ❗ AXI_ERRS_BRESP_STABLE
#### - **Description:** Checks BRESP must remain stable when BVALID is asserted and BREADY Low.

![21](https://github.com/Rex1110/Formal-verification/assets/123956376/6af55ab8-cd40-436e-bd56-c777c6900d97)


### ❗ AXI_ERRS_BVALID_STABLE
#### - **Description:** Once BVALID is asserted, it must remain asserted until BREADY is High.

![22](https://github.com/Rex1110/Formal-verification/assets/123956376/e0ba13a0-036e-4bd8-9e7d-2e49b29ab9df)


## **5. Read address channel cheacks**

### ❗ AXI_ERRM_ARADDR_BOUNDARY
#### - **Description:** A read burst cannot cross a 4 KB boundary.

![23](https://github.com/Rex1110/Formal-verification/assets/123956376/ba642ce7-f47c-4b53-9707-414854cd4702)


### ✅ AXI_ERRM_ARBURST
#### - **Description:** A value of 2'b11 on ARBURST is not permitted when ARVALID is High.

![24](https://github.com/Rex1110/Formal-verification/assets/123956376/7a338fa0-c1c6-47a6-9ca6-00cf3ad04a6d)


### ✅ AXI_ERRM_ARSIZE
#### - **Description:** The size of a read transfer must not exceed the width of the data interface.

![25](https://github.com/Rex1110/Formal-verification/assets/123956376/403fc9eb-f1d2-4eb3-97f5-968c459d8db5)


### ✅ AXI_ERRM_ARVALID_RESET
#### - **Description:** ARVALID is Low for the first cycle after ARESETn goes High.

![26](https://github.com/Rex1110/Formal-verification/assets/123956376/0c01e293-6188-40ac-b00e-9f73f1bc19ca)


### ✅ AXI_ERRM_ARADDR_STABLE
#### - **Description:** ARADDR must remain stable when ARVALID is asserted and ARREADY Low.

![27](https://github.com/Rex1110/Formal-verification/assets/123956376/0f0877b4-cb8b-4961-9d84-7afc4fcb4752)


### ❗ AXI_ERRM_ARBURST_STABLE
#### - **Description:** ARBURST must remain stable when ARVALID is asserted and ARREADY Low.

![28](https://github.com/Rex1110/Formal-verification/assets/123956376/b1daecf4-2247-4e39-bfe8-e1ca57d77d6b)


### ✅ AXI_ERRM_ARID_STABLE
#### - **Description:** ARID must remain stable when ARVALID is asserted and ARREADY Low.

![68](https://github.com/Rex1110/Formal-verification/assets/123956376/dfafe5bc-00f5-48b4-9eb6-7a1ef8b1cf72)


### ✅ AXI_ERRM_ARLEN_STABLE
#### - **Description:** ARLEN must remain stable when ARVALID is asserted and ARREADY Low.

![29](https://github.com/Rex1110/Formal-verification/assets/123956376/bbcda525-153e-4eaf-8443-55c55e29e483)


### ✅ AXI_ERRM_ARSIZE_STABLE
#### - **Description:** ARSIZE must remain stable when ARVALID is asserted and ARREADY Low.

![30](https://github.com/Rex1110/Formal-verification/assets/123956376/65863835-d288-4fa1-9c59-7b9eaaa732e7)


### ✅ AXI_ERRM_ARVALID_STABLE
#### - **Description:** Once ARVALID is asserted, it must remain asserted until ARREADY is High.

![31](https://github.com/Rex1110/Formal-verification/assets/123956376/dc828fde-4b9b-4720-b74e-c3a89abd74d3)


## **6. Read data channel cheacks**

### ✅ AXI_ERRS_RDATA_NUM
#### - **Description:** The number of read data items must match the corresponding ARLEN.

![32](https://github.com/Rex1110/Formal-verification/assets/123956376/ad16c86e-5cbf-463c-8b57-a7d8d447d691)


### ✅ AXI_ERRS_RVALID_RESET
#### - **Description:** RVALID is Low for the first cycle after ARESETn goes High.

![33](https://github.com/Rex1110/Formal-verification/assets/123956376/e33dbe8a-c780-49a6-a200-8b1cc99deec6)


### ❗ AXI_ERRS_RDATA_STABLE
#### - **Description:** RDATA must remain stable when RVALID is asserted and RREADY Low.

![34](https://github.com/Rex1110/Formal-verification/assets/123956376/c6c17448-ec5a-45f5-a6ef-664dd764e9af)


### ❗ AXI_ERRS_RID_STABLE
#### - **Description:** RID must remain stable when RVALID is asserted and RREADY Low.

![35](https://github.com/Rex1110/Formal-verification/assets/123956376/4c15a7a6-12bd-4564-857d-7a8c6227455b)


### ❗ AXI_ERRS_RLAST_STABLE
#### - **Description:** RLAST must remain stable when RVALID is asserted and RREADY Low.

![35](https://github.com/Rex1110/Formal-verification/assets/123956376/4c15a7a6-12bd-4564-857d-7a8c6227455b)

### ❗ AXI_ERRS_RRESP_STABLE
#### - **Description:** RRESP must remain stable when RVALID is asserted and RREADY Low.

![37](https://github.com/Rex1110/Formal-verification/assets/123956376/b902b678-8430-4eeb-8fc2-8eac0b72e4da)


### ❗ AXI_ERRS_RVALID_STABLE
#### - **Description:** Once RVALID is asserted, it must remain asserted until RREADY is High.

![38](https://github.com/Rex1110/Formal-verification/assets/123956376/49192ed0-920c-44c2-8a00-60661d8ef090)


## **7. Simulation-Only Assertions**

### ✅ AXI_ERRM_ARADDR_X
#### - **Description:** When ARVALID is high, a value of X on ARADDR is not permitted.

![39](https://github.com/Rex1110/Formal-verification/assets/123956376/fdd32290-9618-4863-b753-f7a007fcba6a)


### ✅ AXI_ERRM_ARBURST_X
#### - **Description:** When ARVALID is high, a value of X on ARBURST is not permitted.

![40](https://github.com/Rex1110/Formal-verification/assets/123956376/19ea9fe5-0027-407d-a0d2-e4b0ca4b12ef)


### ✅ AXI_ERRM_ARID_X
#### - **Description:** When ARVALID is high, a value of X on ARID is not permitted.

![41](https://github.com/Rex1110/Formal-verification/assets/123956376/9c02102e-e183-4224-8596-f6ad7caa3a6c)

### ✅ AXI_ERRM_ARLEN_X
#### - **Description:** When ARVALID is high, a value of X on ARLEN is not permitted.

![42](https://github.com/Rex1110/Formal-verification/assets/123956376/52f86297-6cf5-4a67-be12-fa65e234c3e8)


### ✅ AXI_ERRM_ARSIZE_X
#### - **Description:** When ARVALID is high, a value of X on ARSIZE is not permitted.

![43](https://github.com/Rex1110/Formal-verification/assets/123956376/0d003933-16bb-451d-9bf1-f855322bc670)


### ✅ AXI_ERRM_ARVALID_X
#### - **Description:** When not in reset, a value of X on ARVALID is not permitted.

![44](https://github.com/Rex1110/Formal-verification/assets/123956376/13416f7e-e026-4d3a-8449-4564523f2216)


### ✅ AXI_ERRM_AWADDR_X
#### - **Description:** When AWVALID is high, a value of X on AWADDR is not permitted.

![45](https://github.com/Rex1110/Formal-verification/assets/123956376/d7bb6146-8448-445e-a4aa-b61d8619261e)


### ✅ AXI_ERRM_AWBURST_X
#### - **Description:** When AWVALID is high, a value of X on AWBURST is not permitted.

![46](https://github.com/Rex1110/Formal-verification/assets/123956376/6ed44d49-1745-45b6-b7b3-1e031aff4438)


### ✅ AXI_ERRM_AWID_X
#### - **Description:** When AWVALID is high, a value of X on AWID is not permitted.

![47](https://github.com/Rex1110/Formal-verification/assets/123956376/8313a6b5-2137-4369-88cb-81f42a8c7478)


### ✅ AXI_ERRM_AWLEN_X
#### - **Description:** When AWVALID is high, a value of X on AWLEN is not permitted.

![48](https://github.com/Rex1110/Formal-verification/assets/123956376/accef590-d88e-4c7e-8fb7-f078c265e6f4)

### ✅ AXI_ERRM_AWSIZE_X
#### - **Description:** When AWVALID is high, a value of X on AWSIZE is not permitted.

![49](https://github.com/Rex1110/Formal-verification/assets/123956376/53a91db7-2a57-4285-a9cc-1992307cebe2)


### ✅ AXI_ERRM_AWVALID_X
#### - **Description:** When not in reset, a value of X on AWVALID is not permitted.

![50](https://github.com/Rex1110/Formal-verification/assets/123956376/5239e9f5-6a85-4db5-88dc-f7a0750878e3)


### ✅ AXI_ERRM_BREADY_X
#### - **Description:** When not in reset, a value of X on BREADY is not permitted.

![51](https://github.com/Rex1110/Formal-verification/assets/123956376/f00a1e1c-6336-4ad5-b4e3-8815cc8fba93)


### ✅ AXI_ERRM_RREADY_X
#### - **Description:** When not in reset, a value of X on RREADY is not permitted.

![52](https://github.com/Rex1110/Formal-verification/assets/123956376/5631e234-b03a-42e3-aacf-1fd4944fbfcd)


### ✅ AXI_ERRM_WDATA_X
#### - **Description:** When WVALID is high, a value of X on active byte lanes of WDATA is not permitted.

![53](https://github.com/Rex1110/Formal-verification/assets/123956376/7cf9a488-4595-415b-998a-5e65d0d0488f)


### ✅ AXI_ERRM_WLAST_X
#### - **Description:** When WVALID is high, a value of X on WLAST is not permitted.

![54](https://github.com/Rex1110/Formal-verification/assets/123956376/0f4f8b3b-5c75-41a6-9e92-08c773f10f1f)


### ✅ AXI_ERRM_WSTRB_X
#### - **Description:** When WVALID is high, a value of X on WSTRB is not permitted.

![55](https://github.com/Rex1110/Formal-verification/assets/123956376/30865b2d-6ed9-4e95-8066-402ed6b593f2)


### ✅ AXI_ERRM_WVALID_X
#### - **Description:** When not in reset, a value of X on WVALID is not permitted.

![56](https://github.com/Rex1110/Formal-verification/assets/123956376/f277ed20-e21d-4e36-b7fd-b020a1404765)


### ✅ AXI_ERRS_ARREADY_X
#### - **Description:** When not in reset, a value of X on ARREADY is not permitted.

![57](https://github.com/Rex1110/Formal-verification/assets/123956376/e5478617-5b8d-43bc-ba1d-04435c07b480)


### ✅ AXI_ERRS_AWREADY_X
#### - **Description:** When not in reset, a value of X on AWREADY is not permitted.

![58](https://github.com/Rex1110/Formal-verification/assets/123956376/23348a65-aad4-4822-b1d5-00c26a0297ee)


### ✅ AXI_ERRS_BID_X
#### - **Description:** When BVALID is high, a value of X on BID is not permitted.

![59](https://github.com/Rex1110/Formal-verification/assets/123956376/2602c1eb-d114-4321-98a3-dd2626799f3b)


### ✅ AXI_ERRS_BRESP_X
#### - **Description:** When BVALID is high, a value of X on BRESP is not permitted.

![60](https://github.com/Rex1110/Formal-verification/assets/123956376/91beb7db-370d-4404-a9b9-67517ba5c229)


### ✅ AXI_ERRS_BVALID_X
#### - **Description:** When BVALID is high, a value of X on BUSER is not permitted.

![61](https://github.com/Rex1110/Formal-verification/assets/123956376/48249633-a61f-4d9b-82ca-f5191333064a)


### ✅ AXI_ERRS_RDATA_X
#### - **Description:** When not in reset, a value of X on BVALID is not permitted.

![62](https://github.com/Rex1110/Formal-verification/assets/123956376/85eb5165-8d18-4c05-a684-c088151f083a)


### ✅ AXI_ERRS_RID_X
#### - **Description:** When RVALID is high, a value of X on RID is not permitted.

![63](https://github.com/Rex1110/Formal-verification/assets/123956376/1638d7e2-4f4c-446e-a0e7-16f09849e058)


### ✅ AXI_ERRS_RLAST_X
#### - **Description:** When RVALID is high, a value of X on RLAST is not permitted.

![64](https://github.com/Rex1110/Formal-verification/assets/123956376/de9d1670-223a-44c8-ad5d-b2b4b5f9716d)


### ✅ AXI_ERRS_RRESP_X
#### - **Description:** When RVALID is high, a value of X on RRESP is not permitted.

![65](https://github.com/Rex1110/Formal-verification/assets/123956376/f1aebe40-b8c5-46ec-9f37-bd5d588a7802)


### ✅ AXI_ERRS_RVALID_X
#### - **Description:** When not in reset, a value of X on RVALID is not permitted.

![66](https://github.com/Rex1110/Formal-verification/assets/123956376/3aaedbba-71dc-48a5-bae7-c8eabf2a6470)


### ✅ AXI_ERRS_WREADY_X
#### - **Description:** When not in reset, a value of X on WREADY is not permitted.

![67](https://github.com/Rex1110/Formal-verification/assets/123956376/44806f6c-1510-4971-98c4-10745d045bec)



## **8. Summary**

斷言失敗皆為跨 4KB boundary，在設計上並沒有特別處理跨 4KB 的問題，如果此次 transaction 會跨越 4KB boundary，則應該要拆成兩個 transaction。

斷言先驗條件未成立的部分為當在 VALID 訊號拉起而 READY 訊號未拉起時，則VALID 訊號必須保持穩定狀態。 然而在設計中，當 VALID 訊號拉起時 READY 訊號已經準備就緒。這並未違反 SPEC，如下。 因此此類斷言由於先驗條件無法滿足，也就不會有後續情況不滿足，均視為通過。

> [!NOTE]
> While it is acceptable to wait for **VALID** to be asserted before asserting **READY**, it is also acceptable to assert **READY** before detecting the corresponding **VALID**. This can result in a more efficient design.

![summary](https://github.com/Rex1110/Formal-verification/assets/123956376/27ea8372-5609-4fd1-926f-5092855a108f)


