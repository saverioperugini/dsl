/* This program implements a stager for up-arrow dialogs using cooperating threads.
 * Each dialog gets its own thread, for example the dialog (W (C a^ b) (C x y)) is
 * staged using seven threads. Each thread has a channel it uses to receive messages
 * from other threads (Actor model of concurrency). A thread understands three types
 * of message:
 *
 *   "con" input -- control is being passed to this thread to stage the input.
 *   "fin"       -- the subdialog to which control was previously passed has finished
 *                  and should not be given control again.
 *   "err"       -- the subdialog to which control was previously passed has failed
 *                  to stage the provided input.
 */

package main

import "fmt"

// con -- control was passed to this dialog
// fin -- the dialog that was just yielded to has finished
// err -- the dialog to which control was given has resulted in an error

// Note: when a dialog finishes, both "fin" and "con" must be passed. "fin" is
// always passed to the parent, but "con" can be passed further up.

type Message struct {
	label string       // can be "con", "fin", or "err"
	input []string     // not used for "fin" and "err" messages
}

func W(mailbox chan Message, parent chan Message, children []chan Message) {
	var previ int = -1
	var input []string = []string{}
	for {
		msg := <-mailbox
		if msg.label == "con" && len(children) > 0 {
			previ = 0
			input = msg.input
			children[0] <- msg
		} else if msg.label == "con" {
			parent <- Message{"fin", []string{}}
			parent <- msg
		} else if msg.label == "fin" {
			children = append(children[:previ], children[previ+1:]...)
		} else if msg.label == "err" && previ == len(children)-1 {
			previ = -1
			parent <- Message{"err", []string{}}
		} else if msg.label == "err" {
			previ = previ + 1
			children[previ] <- Message{"con", input}
		}
	}
}

func C(mailbox chan Message, parent chan Message, children []chan Message) {
	for {
		msg := <-mailbox
		if msg.label == "con" && len(children) > 0 {
			children[0] <- msg
		} else if msg.label == "con" /* && len(children) == 0 */ {
			parent <- Message{"fin", []string{}}
			parent <- msg
		} else if msg.label == "fin" {
			children = children[1:]
		} else if msg.label == "err" {
			parent <- Message{"err", []string{}}
		}
	}
}

func Atomic(mailbox chan Message, parent chan Message, jumpTo chan Message, resp string) {
	for {
		msg := <-mailbox
		if msg.label == "con" {
			if len(msg.input) == 0 {
				parent <- Message{"err", []string{}}
			} else if msg.input[0] == resp {
				parent <- Message{"fin", []string{}}
				jumpTo <- Message{"con", msg.input[1:]}
			} else {
				parent <- Message{"err", []string{}}
			}
		} else {
			// unreachable
		}
	}
}

type Dialog struct {
	mnemonic string
	resp string          // used for Atomic
	subdialogs []Dialog  // used for C, W
	responses []string   // used for I, PE, ... etc.
}

// TODO: up-arrows are not supporated yet
func spawn(d Dialog, parent chan Message) chan Message {
	if d.mnemonic == "Atomic" {
		mailbox := make(chan Message)
		go Atomic(mailbox, parent, parent, d.resp)
		return mailbox
	} else if d.mnemonic == "W" {
		mailbox := make(chan Message)
		children := make([]chan Message, len(d.subdialogs));
		for i, subD := range d.subdialogs {
			children[i] = spawn(subD, mailbox)
		}
		go W(mailbox, parent, children)
		return mailbox
	} else if d.mnemonic == "C" {
		mailbox := make(chan Message)
		children := make([]chan Message, len(d.subdialogs));
		for i, subD := range d.subdialogs {
			children[i] = spawn(subD, mailbox)
		}
		go C(mailbox, parent, children)
		return mailbox
	}
	return make(chan Message) // unreachable
}

// stages the dialog (W (C a b) (C x y))
// on the input "a b x y rest"
func main() {
	dialog := Dialog{"W", "", []Dialog{
		Dialog{"C", "", []Dialog{
			Dialog{"Atomic", "a", []Dialog{}, []string{}},
			Dialog{"Atomic", "b", []Dialog{}, []string{}}}, []string{}},
		Dialog{"C", "", []Dialog{
			Dialog{"Atomic", "x", []Dialog{}, []string{}},
			Dialog{"Atomic", "y", []Dialog{}, []string{}}}, []string{}}}, []string{}}

	root := make(chan Message)
	toplevel := spawn(dialog, root)
	toplevel <- Message{"con", []string{"a", "b", "x", "y", "rest"}}
	fmt.Println(<-root)
	fmt.Println(<-root)

	/*
	root := make(chan Message)
	W1 := make(chan Message)
	C1 := make(chan Message)
	a := make(chan Message)
	go Atomic(a, C1, W1, "a")
	b := make(chan Message)
	go Atomic(b, C1, C1, "b")
	go C(C1, W1, []chan Message{a, b})
	C2 := make(chan Message)
	x := make(chan Message)
	go Atomic(x, C2, C2, "x")
	y := make(chan Message)
	go Atomic(y, C2, C2, "y")
	go C(C2, W1, []chan Message{x, y})
	go W(W1, root, []chan Message{C1, C2})

	W1 <- Message{"con", []string{"a", "x", "y", "b", "rest"}}
	fmt.Println(<-root)
	fmt.Println(<-root)
*/
}
