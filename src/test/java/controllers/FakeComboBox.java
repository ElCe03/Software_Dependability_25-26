package controllers;

public class FakeComboBox {
    private String value;

    public FakeComboBox(String v) {
        this.value = v;
    }

    public String getValue() {
        return value;
    }

    public void setValue(String v) {
        this.value = v;
    }
}
