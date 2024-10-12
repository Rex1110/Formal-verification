## **1. Schematic**
![asyncFIFO](https://github.com/user-attachments/assets/9e317e50-4c2a-4009-b5d1-741d60f3bc6a)

## **2. Specification**

以下都可 config 的
| Name     | Character |
| ---      | ---       |
Depth | 8
Width | 8
Write clock : Read clock | 3 : 4

## **3. Verification points**

### ✅ 1. Neither empty nor full simultaneously 
避免 deadlock
```systemverilog
full_empty: assert property (
  ~(full && empty)
);
```
### ✅ 2. Write full without overflow && Read empty without underflow
建立一個比 asynchronous FIFO 多一個空間的 FIFO，通過對比這兩個 FIFO 的行為來檢測異常。寫入操作時，當 asynchronous FIFO 滿了仍繼續寫入，會覆蓋數據，而額外的 FIFO 因為多了空間不會覆蓋，這樣就能檢測到覆蓋問題。
同樣，讀取操作時，當 asynchronous FIFO 空了仍繼續讀取，會讀到一筆舊值，而額外的 FIFO 因為多了一個空間，最終兩個 FIFO 的數據會不一致，從而發現讀取錯誤。
```systemverilog
data_integrity: assert property (
  (rd_en && ~empty) |-> (queue[rd_ptr_q] == rd_data)
);
```

### ✅ 3. Depth equal to eight
這裡使用 cover property 來確認這個 asynchronous FIFO 確實為深度 8，如果深度不為 8 就不會出現以下狀況，因此 cover 不成立，如果大於 8 則在上條 assertion 會檢測到。
```systemverilog
size1: cover property (
  (wr_ptr_q - rd_ptr_q) == 8
);

size2: cover property (
  (rd_ptr_q - wr_ptr_q) == -1
);
```

## **4. Verification result**

Formal verification tool: **Cadence jasper**

![image](https://github.com/user-attachments/assets/3d6528e9-f260-4ddc-bc4e-604300c1daf7)
