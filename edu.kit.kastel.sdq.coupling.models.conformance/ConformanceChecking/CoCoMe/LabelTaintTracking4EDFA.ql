/**
* @kind path-problem
* @problem.severity warning
* @id labeledtaint
*/

import java
import semmle.code.java.dataflow.TaintTracking

newtype SecurityLevel = 
CashierCustomer() or
BankOtherStore() or
StoreManager() or
BankByStanderCustomer() or
CashierCustomerStoreManager() or
BankCustomerOtherStoreStoreManager() or
BankCashierStoreManager() or
ByStander() or
Cashier() or
CustomerOtherStore() or
ByStanderCustomerOtherStore() or
BankByStanderCashierCustomerStoreManager() or
CustomerStoreManager() or
CashierOtherStoreStoreManager() or
BankByStanderCustomerOtherStore() or
Bank() or
BankByStanderCashierOtherStore() or
BankCashier() or
CashierCustomerOtherStore() or
Customer() or
BankByStanderCashier() or
BankByStanderCustomerOtherStoreStoreManager() or
BankCashierOtherStore() or
BankByStanderOtherStoreStoreManager() or
ByStanderCustomer() or
CashierOtherStore() or
BankCustomerStoreManager() or
CashierCustomerOtherStoreStoreManager() or
ByStanderCashierOtherStore() or
BankCashierCustomerOtherStore() or
BankByStanderCashierCustomer() or
ByStanderCashierOtherStoreStoreManager() or
BankByStanderStoreManager() or
ByStanderCashierCustomerOtherStore() or
BankByStanderCashierOtherStoreStoreManager() or
BankOtherStoreStoreManager() or
BankCustomer() or
BankByStanderCashierCustomerOtherStore() or
ByStanderCashierCustomer() or
ByStanderCashierCustomerStoreManager() or
BankCashierCustomerStoreManager() or
ByStanderCustomerOtherStoreStoreManager() or
BankCustomerOtherStore() or
BankByStander() or
CustomerOtherStoreStoreManager() or
ByStanderCustomerStoreManager() or
ByStanderCashier() or
ByStanderCashierCustomerOtherStoreStoreManager() or
OtherStoreStoreManager() or
BankByStanderCashierCustomerOtherStoreStoreManager() or
ByStanderStoreManager() or
ByStanderOtherStoreStoreManager() or
BankCashierCustomer() or
BankStoreManager() or
OtherStore() or
BankByStanderOtherStore() or
BankByStanderCashierStoreManager() or
ByStanderCashierStoreManager() or
BankCashierCustomerOtherStoreStoreManager() or
CashierStoreManager() or
BankByStanderCustomerStoreManager() or
BankCashierOtherStoreStoreManager() or
ByStanderOtherStore()
or None()

predicate labelParameter(string className, string methodName, string parameterName, DataFlow::Node node){
    
    exists (Class c, Method m, Parameter p | 
        c.contains(m) and 
        c.hasName(className) and 
        m.contains(p) and 
        m.hasName(methodName) and 
        p.hasName(parameterName) 
        and p = node.asParameter()
    ) 
}

predicate labelField(string className, string fieldName, DataFlow::Node node){
	exists(Class c, Field f  | 
		c.hasName(className) and 
		c.contains(f) and
		f.hasName(fieldName) and 
		node.asExpr().(FieldAccess).getField() = f
	)
}

SecurityLevel getLabel(DataFlow::Node node){
	labelParameter("BarCodeScanner", "readBarcode", "barcode", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("BarCodeScanner", "readBarcode", "barcode", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("CardReader", "readCardNumber", "number", node) and result = BankCustomer()  or
	labelParameter("Billing", "readCardNumber", "number", node) and result = BankCustomer()  or
	labelParameter("CardReader", "readPIN", "pin", node) and result = BankCustomer()  or
	labelParameter("Billing", "readPIN", "pin", node) and result = BankCustomer()  or
	labelParameter("CashBox", "acknowladgeCashPayment", "amountPayed", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("GUIStore", "orderProducts", "complexOrder", node) and result = StoreManager()  or
	labelParameter("GUIStore", "getOrder", "orderId", node) and result = StoreManager()  or
	labelParameter("GUIStore", "rollInReceivedOrder", "complexOrderTO", node) and result = StoreManager()  or
	labelParameter("ApplicationStore", "changePrice", "stockItemTO", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("GUIStore", "markProductsUnavailableInStock", "requiredProductsAndAmount", node) and result = StoreManager()  or
	labelParameter("Bank", "requestTransaction", "cardnumber", node) and result = BankCustomer()  or
	labelParameter("Bank", "requestTransaction", "account", node) and result = BankCashierCustomer()  or
	labelParameter("Bank", "requestTransaction", "amount", node) and result = BankByStanderCashierCustomerStoreManager()  or
	labelParameter("Printer", "printShopItem", "name", node) and result = ByStanderCashierCustomer()  or
	labelParameter("Printer", "printShopItem", "price", node) and result = ByStanderCashierCustomer()  or
	labelParameter("Printer", "printShopItem", "vat", node) and result = ByStanderCashierCustomer()  or
	labelParameter("Printer", "printTotal", "grossTotal", node) and result = ByStanderCashierCustomer()  or
	labelParameter("OtherStore", "orderProductsAvailableAtOtherStores", "enterpriseTO", node) and result = OtherStoreStoreManager()  or
	labelParameter("OtherStore", "orderProductsAvailableAtOtherStores", "callingStore", node) and result = OtherStoreStoreManager()  or
	labelParameter("OtherStore", "orderProductsAvailableAtOtherStores", "productAmounts", node) and result = OtherStoreStoreManager()  or
	labelParameter("LightDisplay", "displayShopItem", "id", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("LightDisplay", "displayShopItem", "price", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("LightDisplay", "displayTotal", "grossTotal", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("Printer", "printShopItem", "id", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("Printer", "printShopItem", "name", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("Printer", "printShopItem", "price", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("Printer", "printShopItem", "vat", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("Printer", "printTotal", "netTotal", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("Printer", "printTotal", "grossTotal", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("Printer", "printPaymentCash", "amountPayed", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("Printer", "printPaymentCash", "change", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("Printer", "printPaymentCard", "cardNumber", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("CashDesk", "readBarcode", "barcode", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("CashDesk", "readCardNumber", "number", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("CashDesk", "acknowladgeCashPayment", "amountPayed", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("ApplicationStore", "getProductWithStockItem", "productBarcode", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("ApplicationStore", "bookSale", "sale", node) and result = ByStanderCashierCustomerStoreManager()  or
	labelParameter("ApplicationStore", "orderProducts", "complexOrder", node) and result = StoreManager()  or
	labelParameter("ApplicationStore", "getOrder", "orderId", node) and result = StoreManager()  or
	labelParameter("GUIStore", "rollInReceivedOrder", "complexOrderTO", node) and result = StoreManager()  or
	labelParameter("GUIStore", "markProductsUnavailableInStock", "requiredProductsAndAmount", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryStoreById", "storeId", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryStoreById", "pctx", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryProducts", "storeId", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryProducts", "pctx", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryLowStockItems", "storeId", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryLowStockItems", "pctx", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryLowStockItemsWithRespectToIncomingProducts", "storeId", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryLowStockItemsWithRespectToIncomingProducts", "pctx", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryAllStockItems", "storeId", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryAllStockItems", "pctx", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryStockItem", "stockId", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryStockItem", "pctx", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryStockItemById", "stockId", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryStockItemById", "pctx", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryOrderById", "orderId", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryOrderById", "pctx", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryProductById", "productId", node) and result = StoreManager()  or
	labelParameter("DataStore", "queryProductById", "pctx", node) and result = StoreManager()  or
	labelParameter("DataStore", "getStockItems", "storeId", node) and result = StoreManager()  or
	labelParameter("DataStore", "getStockItems", "productId", node) and result = StoreManager()  or
	labelParameter("DataStore", "getStockItems", "pctx", node) and result = StoreManager() 
	or result = None()
}

predicate hasLabel(DataFlow::Node node){
    getLabel(node) != None()
}

predicate allowedFlows(SecurityLevel source, SecurityLevel sink){
	source = CashierCustomer() and sink = Cashier() or
	source = CashierCustomer() and sink = Customer() or
	source = BankOtherStore() and sink = Bank() or
	source = BankOtherStore() and sink = OtherStore() or
	source = BankByStanderCustomer() and sink = ByStanderCustomer() or
	source = BankByStanderCustomer() and sink = BankCustomer() or
	source = BankByStanderCustomer() and sink = BankByStander() or
	source = CashierCustomerStoreManager() and sink = CashierCustomer() or
	source = CashierCustomerStoreManager() and sink = CustomerStoreManager() or
	source = CashierCustomerStoreManager() and sink = CashierStoreManager() or
	source = BankCustomerOtherStoreStoreManager() and sink = BankCustomerStoreManager() or
	source = BankCustomerOtherStoreStoreManager() and sink = BankOtherStoreStoreManager() or
	source = BankCustomerOtherStoreStoreManager() and sink = BankCustomerOtherStore() or
	source = BankCustomerOtherStoreStoreManager() and sink = CustomerOtherStoreStoreManager() or
	source = BankCashierStoreManager() and sink = BankCashier() or
	source = BankCashierStoreManager() and sink = BankStoreManager() or
	source = BankCashierStoreManager() and sink = CashierStoreManager() or
	source = CustomerOtherStore() and sink = Customer() or
	source = CustomerOtherStore() and sink = OtherStore() or
	source = ByStanderCustomerOtherStore() and sink = CustomerOtherStore() or
	source = ByStanderCustomerOtherStore() and sink = ByStanderCustomer() or
	source = ByStanderCustomerOtherStore() and sink = ByStanderOtherStore() or
	source = BankByStanderCashierCustomerStoreManager() and sink = BankByStanderCashierCustomer() or
	source = BankByStanderCashierCustomerStoreManager() and sink = ByStanderCashierCustomerStoreManager() or
	source = BankByStanderCashierCustomerStoreManager() and sink = BankCashierCustomerStoreManager() or
	source = BankByStanderCashierCustomerStoreManager() and sink = BankByStanderCashierStoreManager() or
	source = BankByStanderCashierCustomerStoreManager() and sink = BankByStanderCustomerStoreManager() or
	source = CustomerStoreManager() and sink = StoreManager() or
	source = CustomerStoreManager() and sink = Customer() or
	source = CashierOtherStoreStoreManager() and sink = CashierOtherStore() or
	source = CashierOtherStoreStoreManager() and sink = OtherStoreStoreManager() or
	source = CashierOtherStoreStoreManager() and sink = CashierStoreManager() or
	source = BankByStanderCustomerOtherStore() and sink = BankByStanderCustomer() or
	source = BankByStanderCustomerOtherStore() and sink = ByStanderCustomerOtherStore() or
	source = BankByStanderCustomerOtherStore() and sink = BankCustomerOtherStore() or
	source = BankByStanderCustomerOtherStore() and sink = BankByStanderOtherStore() or
	source = BankByStanderCashierOtherStore() and sink = BankByStanderCashier() or
	source = BankByStanderCashierOtherStore() and sink = BankCashierOtherStore() or
	source = BankByStanderCashierOtherStore() and sink = ByStanderCashierOtherStore() or
	source = BankByStanderCashierOtherStore() and sink = BankByStanderOtherStore() or
	source = BankCashier() and sink = Cashier() or
	source = BankCashier() and sink = Bank() or
	source = CashierCustomerOtherStore() and sink = CashierCustomer() or
	source = CashierCustomerOtherStore() and sink = CustomerOtherStore() or
	source = CashierCustomerOtherStore() and sink = CashierOtherStore() or
	source = BankByStanderCashier() and sink = BankCashier() or
	source = BankByStanderCashier() and sink = BankByStander() or
	source = BankByStanderCashier() and sink = ByStanderCashier() or
	source = BankByStanderCustomerOtherStoreStoreManager() and sink = BankCustomerOtherStoreStoreManager() or
	source = BankByStanderCustomerOtherStoreStoreManager() and sink = BankByStanderCustomerOtherStore() or
	source = BankByStanderCustomerOtherStoreStoreManager() and sink = BankByStanderOtherStoreStoreManager() or
	source = BankByStanderCustomerOtherStoreStoreManager() and sink = ByStanderCustomerOtherStoreStoreManager() or
	source = BankByStanderCustomerOtherStoreStoreManager() and sink = BankByStanderCustomerStoreManager() or
	source = BankCashierOtherStore() and sink = BankOtherStore() or
	source = BankCashierOtherStore() and sink = BankCashier() or
	source = BankCashierOtherStore() and sink = CashierOtherStore() or
	source = BankByStanderOtherStoreStoreManager() and sink = BankByStanderStoreManager() or
	source = BankByStanderOtherStoreStoreManager() and sink = BankOtherStoreStoreManager() or
	source = BankByStanderOtherStoreStoreManager() and sink = ByStanderOtherStoreStoreManager() or
	source = BankByStanderOtherStoreStoreManager() and sink = BankByStanderOtherStore() or
	source = ByStanderCustomer() and sink = ByStander() or
	source = ByStanderCustomer() and sink = Customer() or
	source = CashierOtherStore() and sink = Cashier() or
	source = CashierOtherStore() and sink = OtherStore() or
	source = BankCustomerStoreManager() and sink = CustomerStoreManager() or
	source = BankCustomerStoreManager() and sink = BankCustomer() or
	source = BankCustomerStoreManager() and sink = BankStoreManager() or
	source = CashierCustomerOtherStoreStoreManager() and sink = CashierCustomerStoreManager() or
	source = CashierCustomerOtherStoreStoreManager() and sink = CashierOtherStoreStoreManager() or
	source = CashierCustomerOtherStoreStoreManager() and sink = CashierCustomerOtherStore() or
	source = CashierCustomerOtherStoreStoreManager() and sink = CustomerOtherStoreStoreManager() or
	source = ByStanderCashierOtherStore() and sink = CashierOtherStore() or
	source = ByStanderCashierOtherStore() and sink = ByStanderCashier() or
	source = ByStanderCashierOtherStore() and sink = ByStanderOtherStore() or
	source = BankCashierCustomerOtherStore() and sink = CashierCustomerOtherStore() or
	source = BankCashierCustomerOtherStore() and sink = BankCashierOtherStore() or
	source = BankCashierCustomerOtherStore() and sink = BankCustomerOtherStore() or
	source = BankCashierCustomerOtherStore() and sink = BankCashierCustomer() or
	source = BankByStanderCashierCustomer() and sink = BankByStanderCustomer() or
	source = BankByStanderCashierCustomer() and sink = BankByStanderCashier() or
	source = BankByStanderCashierCustomer() and sink = ByStanderCashierCustomer() or
	source = BankByStanderCashierCustomer() and sink = BankCashierCustomer() or
	source = ByStanderCashierOtherStoreStoreManager() and sink = CashierOtherStoreStoreManager() or
	source = ByStanderCashierOtherStoreStoreManager() and sink = ByStanderCashierOtherStore() or
	source = ByStanderCashierOtherStoreStoreManager() and sink = ByStanderOtherStoreStoreManager() or
	source = ByStanderCashierOtherStoreStoreManager() and sink = ByStanderCashierStoreManager() or
	source = BankByStanderStoreManager() and sink = BankByStander() or
	source = BankByStanderStoreManager() and sink = ByStanderStoreManager() or
	source = BankByStanderStoreManager() and sink = BankStoreManager() or
	source = ByStanderCashierCustomerOtherStore() and sink = ByStanderCustomerOtherStore() or
	source = ByStanderCashierCustomerOtherStore() and sink = CashierCustomerOtherStore() or
	source = ByStanderCashierCustomerOtherStore() and sink = ByStanderCashierOtherStore() or
	source = ByStanderCashierCustomerOtherStore() and sink = ByStanderCashierCustomer() or
	source = BankByStanderCashierOtherStoreStoreManager() and sink = BankByStanderCashierOtherStore() or
	source = BankByStanderCashierOtherStoreStoreManager() and sink = BankByStanderOtherStoreStoreManager() or
	source = BankByStanderCashierOtherStoreStoreManager() and sink = ByStanderCashierOtherStoreStoreManager() or
	source = BankByStanderCashierOtherStoreStoreManager() and sink = BankByStanderCashierStoreManager() or
	source = BankByStanderCashierOtherStoreStoreManager() and sink = BankCashierOtherStoreStoreManager() or
	source = BankOtherStoreStoreManager() and sink = BankOtherStore() or
	source = BankOtherStoreStoreManager() and sink = OtherStoreStoreManager() or
	source = BankOtherStoreStoreManager() and sink = BankStoreManager() or
	source = BankCustomer() and sink = Bank() or
	source = BankCustomer() and sink = Customer() or
	source = BankByStanderCashierCustomerOtherStore() and sink = BankByStanderCustomerOtherStore() or
	source = BankByStanderCashierCustomerOtherStore() and sink = BankByStanderCashierOtherStore() or
	source = BankByStanderCashierCustomerOtherStore() and sink = BankCashierCustomerOtherStore() or
	source = BankByStanderCashierCustomerOtherStore() and sink = BankByStanderCashierCustomer() or
	source = BankByStanderCashierCustomerOtherStore() and sink = ByStanderCashierCustomerOtherStore() or
	source = ByStanderCashierCustomer() and sink = CashierCustomer() or
	source = ByStanderCashierCustomer() and sink = ByStanderCustomer() or
	source = ByStanderCashierCustomer() and sink = ByStanderCashier() or
	source = ByStanderCashierCustomerStoreManager() and sink = CashierCustomerStoreManager() or
	source = ByStanderCashierCustomerStoreManager() and sink = ByStanderCashierCustomer() or
	source = ByStanderCashierCustomerStoreManager() and sink = ByStanderCustomerStoreManager() or
	source = ByStanderCashierCustomerStoreManager() and sink = ByStanderCashierStoreManager() or
	source = BankCashierCustomerStoreManager() and sink = CashierCustomerStoreManager() or
	source = BankCashierCustomerStoreManager() and sink = BankCashierStoreManager() or
	source = BankCashierCustomerStoreManager() and sink = BankCustomerStoreManager() or
	source = BankCashierCustomerStoreManager() and sink = BankCashierCustomer() or
	source = ByStanderCustomerOtherStoreStoreManager() and sink = ByStanderCustomerOtherStore() or
	source = ByStanderCustomerOtherStoreStoreManager() and sink = CustomerOtherStoreStoreManager() or
	source = ByStanderCustomerOtherStoreStoreManager() and sink = ByStanderCustomerStoreManager() or
	source = ByStanderCustomerOtherStoreStoreManager() and sink = ByStanderOtherStoreStoreManager() or
	source = BankCustomerOtherStore() and sink = BankOtherStore() or
	source = BankCustomerOtherStore() and sink = CustomerOtherStore() or
	source = BankCustomerOtherStore() and sink = BankCustomer() or
	source = BankByStander() and sink = ByStander() or
	source = BankByStander() and sink = Bank() or
	source = CustomerOtherStoreStoreManager() and sink = CustomerOtherStore() or
	source = CustomerOtherStoreStoreManager() and sink = CustomerStoreManager() or
	source = CustomerOtherStoreStoreManager() and sink = OtherStoreStoreManager() or
	source = ByStanderCustomerStoreManager() and sink = CustomerStoreManager() or
	source = ByStanderCustomerStoreManager() and sink = ByStanderCustomer() or
	source = ByStanderCustomerStoreManager() and sink = ByStanderStoreManager() or
	source = ByStanderCashier() and sink = ByStander() or
	source = ByStanderCashier() and sink = Cashier() or
	source = ByStanderCashierCustomerOtherStoreStoreManager() and sink = CashierCustomerOtherStoreStoreManager() or
	source = ByStanderCashierCustomerOtherStoreStoreManager() and sink = ByStanderCashierOtherStoreStoreManager() or
	source = ByStanderCashierCustomerOtherStoreStoreManager() and sink = ByStanderCashierCustomerOtherStore() or
	source = ByStanderCashierCustomerOtherStoreStoreManager() and sink = ByStanderCashierCustomerStoreManager() or
	source = ByStanderCashierCustomerOtherStoreStoreManager() and sink = ByStanderCustomerOtherStoreStoreManager() or
	source = OtherStoreStoreManager() and sink = StoreManager() or
	source = OtherStoreStoreManager() and sink = OtherStore() or
	source = BankByStanderCashierCustomerOtherStoreStoreManager() and sink = BankByStanderCashierCustomerStoreManager() or
	source = BankByStanderCashierCustomerOtherStoreStoreManager() and sink = BankByStanderCustomerOtherStoreStoreManager() or
	source = BankByStanderCashierCustomerOtherStoreStoreManager() and sink = BankByStanderCashierOtherStoreStoreManager() or
	source = BankByStanderCashierCustomerOtherStoreStoreManager() and sink = BankByStanderCashierCustomerOtherStore() or
	source = BankByStanderCashierCustomerOtherStoreStoreManager() and sink = ByStanderCashierCustomerOtherStoreStoreManager() or
	source = BankByStanderCashierCustomerOtherStoreStoreManager() and sink = BankCashierCustomerOtherStoreStoreManager() or
	source = ByStanderStoreManager() and sink = StoreManager() or
	source = ByStanderStoreManager() and sink = ByStander() or
	source = ByStanderOtherStoreStoreManager() and sink = OtherStoreStoreManager() or
	source = ByStanderOtherStoreStoreManager() and sink = ByStanderStoreManager() or
	source = ByStanderOtherStoreStoreManager() and sink = ByStanderOtherStore() or
	source = BankCashierCustomer() and sink = CashierCustomer() or
	source = BankCashierCustomer() and sink = BankCashier() or
	source = BankCashierCustomer() and sink = BankCustomer() or
	source = BankStoreManager() and sink = StoreManager() or
	source = BankStoreManager() and sink = Bank() or
	source = BankByStanderOtherStore() and sink = BankOtherStore() or
	source = BankByStanderOtherStore() and sink = BankByStander() or
	source = BankByStanderOtherStore() and sink = ByStanderOtherStore() or
	source = BankByStanderCashierStoreManager() and sink = BankCashierStoreManager() or
	source = BankByStanderCashierStoreManager() and sink = BankByStanderCashier() or
	source = BankByStanderCashierStoreManager() and sink = BankByStanderStoreManager() or
	source = BankByStanderCashierStoreManager() and sink = ByStanderCashierStoreManager() or
	source = ByStanderCashierStoreManager() and sink = ByStanderCashier() or
	source = ByStanderCashierStoreManager() and sink = ByStanderStoreManager() or
	source = ByStanderCashierStoreManager() and sink = CashierStoreManager() or
	source = BankCashierCustomerOtherStoreStoreManager() and sink = BankCustomerOtherStoreStoreManager() or
	source = BankCashierCustomerOtherStoreStoreManager() and sink = CashierCustomerOtherStoreStoreManager() or
	source = BankCashierCustomerOtherStoreStoreManager() and sink = BankCashierCustomerOtherStore() or
	source = BankCashierCustomerOtherStoreStoreManager() and sink = BankCashierCustomerStoreManager() or
	source = BankCashierCustomerOtherStoreStoreManager() and sink = BankCashierOtherStoreStoreManager() or
	source = CashierStoreManager() and sink = StoreManager() or
	source = CashierStoreManager() and sink = Cashier() or
	source = BankByStanderCustomerStoreManager() and sink = BankByStanderCustomer() or
	source = BankByStanderCustomerStoreManager() and sink = BankCustomerStoreManager() or
	source = BankByStanderCustomerStoreManager() and sink = BankByStanderStoreManager() or
	source = BankByStanderCustomerStoreManager() and sink = ByStanderCustomerStoreManager() or
	source = BankCashierOtherStoreStoreManager() and sink = BankCashierStoreManager() or
	source = BankCashierOtherStoreStoreManager() and sink = CashierOtherStoreStoreManager() or
	source = BankCashierOtherStoreStoreManager() and sink = BankCashierOtherStore() or
	source = BankCashierOtherStoreStoreManager() and sink = BankOtherStoreStoreManager() or
	source = ByStanderOtherStore() and sink = ByStander() or
	source = ByStanderOtherStore() and sink = OtherStore()
	or getLevelAsString(source) = getLevelAsString(sink) 
	or exists(SecurityLevel l | allowedFlows(source, l) and allowedFlows(l, sink)) 
	or none()
}

predicate isFlowAllowed(DataFlow::Node source, DataFlow::Node sink){
   allowedFlows(getLabel(source), getLabel(sink))
}   

module MyFlowConfiguration implements DataFlow::ConfigSig {
		
		    predicate isSource(DataFlow::Node source){
		        hasLabel(source)
		    }
		
		    predicate isSink(DataFlow::Node sink) {
		        hasLabel(sink)
		    }
	}

string getLevelAsString(SecurityLevel level){
		level = CashierCustomer() and result = "Cashier;Customer" or
		level = BankOtherStore() and result = "Bank;OtherStore" or
		level = StoreManager() and result = "StoreManager" or
		level = BankByStanderCustomer() and result = "Bank;ByStander;Customer" or
		level = CashierCustomerStoreManager() and result = "Cashier;Customer;StoreManager" or
		level = BankCustomerOtherStoreStoreManager() and result = "Bank;Customer;OtherStore;StoreManager" or
		level = BankCashierStoreManager() and result = "Bank;Cashier;StoreManager" or
		level = ByStander() and result = "ByStander" or
		level = Cashier() and result = "Cashier" or
		level = CustomerOtherStore() and result = "Customer;OtherStore" or
		level = ByStanderCustomerOtherStore() and result = "ByStander;Customer;OtherStore" or
		level = BankByStanderCashierCustomerStoreManager() and result = "Bank;ByStander;Cashier;Customer;StoreManager" or
		level = CustomerStoreManager() and result = "Customer;StoreManager" or
		level = CashierOtherStoreStoreManager() and result = "Cashier;OtherStore;StoreManager" or
		level = BankByStanderCustomerOtherStore() and result = "Bank;ByStander;Customer;OtherStore" or
		level = Bank() and result = "Bank" or
		level = BankByStanderCashierOtherStore() and result = "Bank;ByStander;Cashier;OtherStore" or
		level = BankCashier() and result = "Bank;Cashier" or
		level = CashierCustomerOtherStore() and result = "Cashier;Customer;OtherStore" or
		level = Customer() and result = "Customer" or
		level = BankByStanderCashier() and result = "Bank;ByStander;Cashier" or
		level = BankByStanderCustomerOtherStoreStoreManager() and result = "Bank;ByStander;Customer;OtherStore;StoreManager" or
		level = BankCashierOtherStore() and result = "Bank;Cashier;OtherStore" or
		level = BankByStanderOtherStoreStoreManager() and result = "Bank;ByStander;OtherStore;StoreManager" or
		level = ByStanderCustomer() and result = "ByStander;Customer" or
		level = CashierOtherStore() and result = "Cashier;OtherStore" or
		level = BankCustomerStoreManager() and result = "Bank;Customer;StoreManager" or
		level = CashierCustomerOtherStoreStoreManager() and result = "Cashier;Customer;OtherStore;StoreManager" or
		level = ByStanderCashierOtherStore() and result = "ByStander;Cashier;OtherStore" or
		level = BankCashierCustomerOtherStore() and result = "Bank;Cashier;Customer;OtherStore" or
		level = BankByStanderCashierCustomer() and result = "Bank;ByStander;Cashier;Customer" or
		level = ByStanderCashierOtherStoreStoreManager() and result = "ByStander;Cashier;OtherStore;StoreManager" or
		level = BankByStanderStoreManager() and result = "Bank;ByStander;StoreManager" or
		level = ByStanderCashierCustomerOtherStore() and result = "ByStander;Cashier;Customer;OtherStore" or
		level = BankByStanderCashierOtherStoreStoreManager() and result = "Bank;ByStander;Cashier;OtherStore;StoreManager" or
		level = BankOtherStoreStoreManager() and result = "Bank;OtherStore;StoreManager" or
		level = BankCustomer() and result = "Bank;Customer" or
		level = BankByStanderCashierCustomerOtherStore() and result = "Bank;ByStander;Cashier;Customer;OtherStore" or
		level = ByStanderCashierCustomer() and result = "ByStander;Cashier;Customer" or
		level = ByStanderCashierCustomerStoreManager() and result = "ByStander;Cashier;Customer;StoreManager" or
		level = BankCashierCustomerStoreManager() and result = "Bank;Cashier;Customer;StoreManager" or
		level = ByStanderCustomerOtherStoreStoreManager() and result = "ByStander;Customer;OtherStore;StoreManager" or
		level = BankCustomerOtherStore() and result = "Bank;Customer;OtherStore" or
		level = BankByStander() and result = "Bank;ByStander" or
		level = CustomerOtherStoreStoreManager() and result = "Customer;OtherStore;StoreManager" or
		level = ByStanderCustomerStoreManager() and result = "ByStander;Customer;StoreManager" or
		level = ByStanderCashier() and result = "ByStander;Cashier" or
		level = ByStanderCashierCustomerOtherStoreStoreManager() and result = "ByStander;Cashier;Customer;OtherStore;StoreManager" or
		level = OtherStoreStoreManager() and result = "OtherStore;StoreManager" or
		level = BankByStanderCashierCustomerOtherStoreStoreManager() and result = "Bank;ByStander;Cashier;Customer;OtherStore;StoreManager" or
		level = ByStanderStoreManager() and result = "ByStander;StoreManager" or
		level = ByStanderOtherStoreStoreManager() and result = "ByStander;OtherStore;StoreManager" or
		level = BankCashierCustomer() and result = "Bank;Cashier;Customer" or
		level = BankStoreManager() and result = "Bank;StoreManager" or
		level = OtherStore() and result = "OtherStore" or
		level = BankByStanderOtherStore() and result = "Bank;ByStander;OtherStore" or
		level = BankByStanderCashierStoreManager() and result = "Bank;ByStander;Cashier;StoreManager" or
		level = ByStanderCashierStoreManager() and result = "ByStander;Cashier;StoreManager" or
		level = BankCashierCustomerOtherStoreStoreManager() and result = "Bank;Cashier;Customer;OtherStore;StoreManager" or
		level = CashierStoreManager() and result = "Cashier;StoreManager" or
		level = BankByStanderCustomerStoreManager() and result = "Bank;ByStander;Customer;StoreManager" or
		level = BankCashierOtherStoreStoreManager() and result = "Bank;Cashier;OtherStore;StoreManager" or
		level = ByStanderOtherStore() and result = "ByStander;OtherStore"
	}

string getNodeLevelAsString(DataFlow::Node node){
	    	result = getLevelAsString(getLabel(node))
}

string printResult(MyTaintFlow::PathNode source, MyTaintFlow::PathNode sink){
    result = 
    "(" 
    + printResult(source.getNode()) 
    +"," 
    + getNodeLevelAsString(source.getNode()) 
    + ")" 
    + "-> (" 
    + printResult(sink.getNode()) 
    + "," 
    + getNodeLevelAsString(sink.getNode()) 
    +")"
}

string printResult(DataFlow::Node node){
    result = printField(node) or
    result = printParameter(node)
}

string printParameter(DataFlow::Node node){
    result = node.getEnclosingCallable().getDeclaringType().getPackage() + "." 
        + node.getEnclosingCallable().getDeclaringType().getName() + "::" 
        + node.getEnclosingCallable().getName()
        + "."
        + node.asParameter().getName() + ":"
    	+ node.asParameter().getType().getName()
}

string printField(DataFlow::Node node){
     result = node.getEnclosingCallable().getDeclaringType().getPackage() + "." 
        + node.getEnclosingCallable().getDeclaringType().getName() + "!" 
        + node.asExpr().(FieldAccess).getField().getName() + ":" 
    	+ node.asExpr().(FieldAccess).getField().getType().getName()
}

predicate notEqualElements(DataFlow::Node node1, DataFlow::Node node2){
    node1.getEnclosingCallable().getDeclaringType().getPackage() != node2.getEnclosingCallable().getDeclaringType().getPackage() 
    or
    node1.getEnclosingCallable().getDeclaringType().getName() != node2.getEnclosingCallable().getDeclaringType().getName() 
    or 
    node1.asExpr().(FieldAccess).getField().getName() != node2.asExpr().(FieldAccess).getField().getName()
    or 
    node1.getEnclosingCallable().getName() != node2.getEnclosingCallable().getName()
    or node1.asParameter().getName() != node2.asParameter().getName()
}

module MyTaintFlow = TaintTracking::Global<MyFlowConfiguration>;
import MyTaintFlow::PathGraph

from MyTaintFlow::PathNode source, MyTaintFlow::PathNode sink
where MyTaintFlow::flowPath(source, sink) and source != sink and not isFlowAllowed(source.getNode(), sink.getNode()) and notEqualElements(source.getNode(), sink.getNode())
select sink.getNode(), source, sink, printResult(source, sink)