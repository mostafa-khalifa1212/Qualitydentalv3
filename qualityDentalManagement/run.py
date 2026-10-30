from app import app
import webbrowser, threading, time
if __name__ == "__main__":
    def open_browser():
        time.sleep(1.2)
        webbrowser.open("http://127.0.0.1:8000")
    threading.Thread(target=open_browser, daemon=True).start()
    app.run(host="0.0.0.0", port=8000, debug=False, threaded=True)
