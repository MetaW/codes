//
//  CollisionAndContactScene.swift
//  firstTry
//
//  Created by wanglulu on 15/12/10.
//  Copyright © 2015年 wanglulu. All rights reserved.
//
/*****************************************************
本Demo包含Sprite的碰撞(collision)控制和Sprite的接触事件(contact),
以及音效的使用方法：

1.  参与碰撞或接触事件的前提条件是Sprite要有physicalBody
2.  每个physicalBody都有三个属性：
    categoryBitMask
    collisionBitMask
    contactTestBitMask
    这三个属性都是32位的UInt32的数据类型，背后的工作机制是位运算。
    
    其中：
2.1 categoryBitMask表明该Sprite属于哪个类别，一个类别占一位，最多
    有32个类别的Sprite，类别通常由一个枚举体声明以方便后面使用，本
    Demo中类别由spriteCategory枚举体声明。categoryBitMask的默认
    值为0xFFFFFFFF，即默认为每一个类别

2.2 collisionBitMask表明与哪些类别的Sprite接近后会有碰撞产生，
    它的默认值为0xFFFFFFFF，即与所有类别的Sprite都产生碰撞。
    当两物体接近时，一物体的collisionBitMask与另一物体的
    categoryBitMask相与，
    1)两物体的结果都不为0时才会发生碰撞，
    2)结果都为零时两物体相互不影响直接穿过，
    3)结果一个为0另一个不为0时碰撞会产生,但只对运算结果不为零的有物理
    效果，运算结果为零的此时好像质量为无穷大,碰撞不会对他产生任何物理影响

2.3 contactTestBitMask表明与哪些类别的物体接触时会触发事件，
    !!!事件的触发与是否碰撞毫无关系只和是否接触有关!!!，两物体接触时，
    无论是碰撞还是穿过，都相互将自己的contactTestBitMask与对方的
    categoryBitMask相与，只要结果有一个不为0，接触事件就会触发。
    实现接触事件必须先接受SKPhysicsContactDelegate接口，再设置代理
    最后实现didBeginContact方法。每次触发接触事件都会调用didBeginContact
    方法，该方法有一个contact参数，它的bodyA,bodyB属性分别就是发生接触事件
    的两个物体，由此可在该方法中实现自己的事件内容。

------------------------------------------------------
音效的使用：
1.  音效用SKAction来创建，像使用其他动作一样来使用音效action

2.  ！！！在程序中要尽量将对象一次创建多次使用，尤其是音效这种
    使用率高，占内存又大的对象。但哪些占内存大又不经常用到也不一定
    会用到的对象应在使用时再创建，并且用完后就释放，swift中的延迟存储属性
    就自动实现了这一点。

******************************************************/
import Foundation
import SpriteKit

//
enum spriteCategory:UInt32{
    case redball = 1
    case blueball = 2
    case yellowball = 4
    case worldEdge = 8
}

class CollisionAndContactScene:SKScene, SKPhysicsContactDelegate{
    
    //在这里创建音效动作，在后面多次使用，不要用一次就创建一次。
    //这里第二个参数指名了该动作的完成时间，如果填true则动作等音效放完才结束，如果填false则
    //音效一开始播放动作就结束，如果后面还有别的动作就会立刻执行，而音效在另一个线程自己播放。
    var hitSound = SKAction.playSoundFileNamed("hit.wav", waitForCompletion: false)
    
    override func didMoveToView(view: SKView) {
        //
        self.physicsWorld.contactDelegate = self

        self.size = CGSize(width: 900, height: 800)
        
        self.physicsWorld.gravity = CGVector(dx: 0, dy: -10)
        let sceneBody = SKPhysicsBody(edgeLoopFromRect: self.frame)
        sceneBody.friction = 0
        sceneBody.restitution = 1
        self.physicsBody = sceneBody
        //
        self.physicsBody?.categoryBitMask = spriteCategory.worldEdge.rawValue
        
        let red = SKShapeNode(circleOfRadius: 50)
        red.fillColor = SKColor.redColor()
        red.position = CGPoint(x: 300, y: 500)
        red.physicsBody = SKPhysicsBody(circleOfRadius: 50)
        red.physicsBody?.dynamic = true
        red.physicsBody?.restitution = 1
        red.physicsBody?.linearDamping = 0
        red.physicsBody?.velocity = CGVector(dx: 200, dy: 0)

        //
        red.physicsBody?.categoryBitMask = spriteCategory.redball.rawValue
        red.physicsBody?.collisionBitMask =
            spriteCategory.worldEdge.rawValue |
            spriteCategory.blueball.rawValue
        red.physicsBody?.contactTestBitMask = spriteCategory.blueball.rawValue

        self.addChild(red)
        
        let blue = SKShapeNode(circleOfRadius: 50)
        blue.fillColor = SKColor.blueColor()
        blue.position = CGPoint(x: 600, y: 500)
        blue.physicsBody = SKPhysicsBody(circleOfRadius: 50)
        blue.physicsBody?.dynamic = true
        blue.physicsBody?.restitution = 1
        blue.physicsBody?.linearDamping = 0
        blue.physicsBody?.velocity = CGVector(dx: -200, dy: 0)

        //
        blue.physicsBody?.categoryBitMask = spriteCategory.blueball.rawValue
        blue.physicsBody?.collisionBitMask =
            spriteCategory.worldEdge.rawValue |
            spriteCategory.redball.rawValue
        
        blue.physicsBody?.contactTestBitMask = spriteCategory.redball.rawValue
        
        self.addChild(blue)
    }
    
    //
    func didBeginContact(contact: SKPhysicsContact) {
        
        //
        print(contact.bodyA.categoryBitMask)
        print(contact.bodyB.categoryBitMask)
        print("collision! \n")
        self.runAction(hitSound)
    }
    
    
}