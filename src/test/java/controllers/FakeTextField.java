package controllers;

public class FakeTextField {
    private String text;

    public FakeTextField(String t) {
        this.text = t;
    }

    public String getText() {
        return text;
    }

    public void clear() {
        text = "";
    }
}
